import itertools
import os
from queue import Empty, SimpleQueue
from threading import Lock, Thread
from time import sleep, time
import sys
import numpy as np
import redis
import orjson
from larch import pickle
import torch
from torch.utils.data import DataLoader, Dataset
import wandb


import guiding_model

device = guiding_model.device


def current_grammar_loop(
    redis_db, model, model_lock, current_grammar, embeddings_cache
):
    redis_conn = redis.Redis(host="localhost", port=6379, db=redis_db)
    while True:
        new_grammar_str = redis_conn.get("set_current_grammar")
        if not new_grammar_str:
            sleep(0.001)
            continue
        new_grammar = orjson.loads(new_grammar_str)
        new_funcs = [f for f in new_grammar if f not in embeddings_cache]

        if new_funcs:
            with model_lock:
                new_funcs_embedding = model.get_embedding(new_funcs).cpu()
            for i, f in enumerate(new_funcs):
                embeddings_cache[f] = new_funcs_embedding[i, :]

        with model_lock:
            grammar_func_encodings = torch.stack(
                [embeddings_cache[f] for f in new_grammar]
            ).to(device)

            grammar_encodings = torch.mean(grammar_func_encodings, dim=0)

        current_grammar[0] = grammar_func_encodings, grammar_encodings
        redis_conn.delete("set_current_grammar")


def fetching_loop(
    redis_db, queues, embeddings_cache, inputs_cache, outputs_cache, finished_tasks
):
    redis_conn = redis.Redis(host="localhost", port=6379, db=redis_db)
    it = 0
    while True:
        start = time()
        payload_str = redis_conn.lpop("requests")
        if not payload_str:
            sleep(0.001)
            continue
        payload = orjson.loads(payload_str)
        if payload["task_name"] in finished_tasks:
            continue

        trace_val = payload["trace_val"]

        new_trace_vals = set(v for v in trace_val[0] if v not in embeddings_cache)

        out_queue = "processing_queue"
        it += 1

        if new_trace_vals:
            for v in new_trace_vals:
                queues["embeddings_queue"].put(
                    {
                        "task_name": payload["task_name"],
                        "trace_val": v,
                    }
                )

            out_queue = "waiting_for_embedding"
            payload["needs_embedding"] = True

        if payload["task_name"] not in outputs_cache:
            queues["outputs_queue"].put(
                {"task_name": payload["task_name"], "output": payload["output"]},
            )
            out_queue = "waiting_for_outputs"
            payload["needs_outputs"] = True

        if payload["task_name"] not in inputs_cache:
            queues["inputs_queue"].put(
                {"task_name": payload["task_name"], "inputs": payload["inputs"]}
            )
            out_queue = "waiting_for_inputs"
            payload["needs_inputs"] = True

        payload["start_time"] = start
        payload["fetch_time"] = time() - start
        if out_queue == "processing_queue":
            queues[out_queue].put(payload)
        else:
            queues[out_queue][0].put(payload)


def check_next_input_batches(
    queues,
    inputs_cache,
    finished_tasks,
    run_time,
    preprocessing_time,
    start,
):
    while True:
        if len(queues["waiting_for_inputs"][1]) > 0:
            payload = queues["waiting_for_inputs"][1].pop()
        else:
            try:
                payload = queues["waiting_for_inputs"][0].get_nowait()
            except Empty:
                break

        task_name = payload["task_name"]
        if task_name in finished_tasks:
            continue

        if task_name not in inputs_cache:
            queues["waiting_for_inputs"][1].append(payload)
            break

        if "needs_outputs" in payload:
            next_queue = "waiting_for_outputs"
        elif "needs_embedding" in payload:
            next_queue = "waiting_for_embedding"
        else:
            next_queue = "processing_queue"

        payload["input_time"] = run_time
        payload["input_preprocessing_time"] = preprocessing_time
        payload["fetch_time"] += time() - start
        if next_queue == "processing_queue":
            queues[next_queue].put(payload)
        else:
            queues[next_queue][0].put(payload)


def preprocess_inputs_batch(inputs_batch):
    input_grids = [
        [[np.array(example) for example in var] for var in v["inputs"]]
        for v in inputs_batch
    ]

    max_x = max(
        example.shape[0] for entry in input_grids for var in entry for example in var
    )
    max_y = max(
        example.shape[1] for entry in input_grids for var in entry for example in var
    )
    example_count = sum(len(var) for entry in input_grids for var in entry)
    combined_batch = np.zeros((example_count, 10, max_x, max_y), dtype=np.float32)
    mask = np.zeros((example_count, 1, max_x, max_y), dtype=np.float32)
    subbatch_mask = np.zeros((example_count, len(input_grids)), dtype=np.float32)

    i = 0
    for j, entry in enumerate(input_grids):
        entry_size = sum(len(var) for var in entry)
        entry_mask = np.zeros((entry_size, len(entry)), dtype=np.float32)
        m = 0
        for k, var in enumerate(entry):
            for example in var:
                combined_batch[i, example, : example.shape[0], : example.shape[1]] = 1
                mask[i, 0, : example.shape[0], : example.shape[1]] = 1
                i += 1
            entry_mask[m : m + len(var), k] = 1 / len(var)
            m += len(var)

        subbatch_mask[i - entry_size : i, j] = np.matmul(
            entry_mask, np.repeat(1 / len(entry), len(entry))
        )

    return combined_batch, mask, subbatch_mask


def inputs_loop(queues, model, model_lock, inputs_cache, finished_tasks):
    try:
        batch_size = 32
        while True:
            start = time()
            inputs_batch = []
            task_names = set()
            while len(inputs_batch) < batch_size:
                try:
                    new_payload = queues["inputs_queue"].get_nowait()
                    task_name = new_payload["task_name"]
                    if (
                        task_name in finished_tasks
                        or task_name in task_names
                        or task_name in inputs_cache
                    ):
                        continue
                    task_names.add(task_name)
                    inputs_batch.append(new_payload)
                except Empty:
                    break
            if not inputs_batch:
                check_next_input_batches(
                    queues, inputs_cache, finished_tasks, 0.0, 0.0, start
                )
                sleep(0.001)
                continue

            # print("Processing inputs batch")
            start_processing = time()

            combined_inputs_batch = preprocess_inputs_batch(inputs_batch)

            preprocessing_time = time() - start_processing

            with model_lock:
                start_processing = time()
                combined_inputs_batch = model.transfer_to_device(combined_inputs_batch)

                with torch.no_grad():
                    input_encodings = model.input_output_encoder(*combined_inputs_batch)

                for i, v in enumerate(inputs_batch):
                    inputs_cache[v["task_name"]] = input_encodings[i, :]

                processing_time = time() - start_processing

            wandb.log(
                {
                    "inputs_processing_time": processing_time,
                    "inputs_preprocessing_time": preprocessing_time,
                    "inputs_batch_size": len(inputs_batch),
                }
            )
            # print("Processed inputs batch")
            check_next_input_batches(
                queues,
                inputs_cache,
                finished_tasks,
                processing_time,
                preprocessing_time,
                start,
            )
    finally:
        print("Exiting inputs loop")


def check_next_output_batches(
    queues, outputs_cache, finished_tasks, run_time, preprocessing_time, start
):
    while True:
        if len(queues["waiting_for_outputs"][1]) > 0:
            payload = queues["waiting_for_outputs"][1].pop()
        else:
            try:
                payload = queues["waiting_for_outputs"][0].get_nowait()
            except Empty:
                break

        task_name = payload["task_name"]
        if task_name in finished_tasks:
            continue

        if task_name not in outputs_cache:
            queues["waiting_for_outputs"][1].append(payload)
            break

        if "needs_embedding" in payload:
            next_queue = "waiting_for_embedding"
        else:
            next_queue = "processing_queue"

        payload["output_time"] = run_time
        payload["output_preprocessing_time"] = preprocessing_time
        payload["fetch_time"] += time() - start
        if next_queue == "processing_queue":
            queues[next_queue].put(payload)
        else:
            queues[next_queue][0].put(payload)


def preprocess_outputs_batch(outputs_batch):
    output_grids = [
        [np.array(example) for example in v["output"]] for v in outputs_batch
    ]

    max_x = max(example.shape[0] for entry in output_grids for example in entry)
    max_y = max(example.shape[1] for entry in output_grids for example in entry)
    example_count = sum(len(entry) for entry in output_grids)

    combined_batch = np.zeros((example_count, 10, max_x, max_y), dtype=np.float32)
    mask = np.zeros((example_count, 1, max_x, max_y), dtype=np.float32)
    subbatch_mask = np.zeros((example_count, len(output_grids)), dtype=np.float32)

    i = 0
    for j, entry in enumerate(output_grids):
        for example in entry:
            combined_batch[i, example, : example.shape[0], : example.shape[1]] = 1
            mask[i, 0, : example.shape[0], : example.shape[1]] = 1
            i += 1

        subbatch_mask[i - len(entry) : i, j] = 1 / len(entry)

    return combined_batch, mask, subbatch_mask


def outputs_loop(queues, model, model_lock, outputs_cache, finished_tasks):
    try:
        batch_size = 32
        while True:
            start = time()
            outputs_batch = []
            task_names = set()
            while len(outputs_batch) < batch_size:
                try:
                    new_payload = queues["outputs_queue"].get_nowait()
                    task_name = new_payload["task_name"]
                    if (
                        task_name in finished_tasks
                        or task_name in task_names
                        or task_name in outputs_cache
                    ):
                        continue
                    task_names.add(task_name)
                    outputs_batch.append(new_payload)
                except Empty:
                    break
            if not outputs_batch:
                check_next_output_batches(
                    queues, outputs_cache, finished_tasks, 0.0, 0.0, start
                )
                sleep(0.001)
                continue

            # print("Processing outputs batch")

            start_processing = time()

            combined_outputs_batch = preprocess_outputs_batch(outputs_batch)

            preprocessing_time = time() - start_processing
            with model_lock:
                start_processing = time()
                combined_outputs_batch = model.transfer_to_device(
                    combined_outputs_batch
                )
                with torch.no_grad():
                    output_encodings = model.input_output_encoder(
                        *combined_outputs_batch
                    )

                for i, v in enumerate(outputs_batch):
                    outputs_cache[v["task_name"]] = output_encodings[i, :]

                run_time = time() - start_processing

            wandb.log(
                {
                    "outputs_processing_time": run_time,
                    "outputs_preprocessing_time": preprocessing_time,
                    "outputs_batch_size": len(outputs_batch),
                }
            )
            # print("Processed outputs batch")
            check_next_output_batches(
                queues,
                outputs_cache,
                finished_tasks,
                run_time,
                preprocessing_time,
                start,
            )
    finally:
        print("Exiting output loop")


def check_next_embedding_batches(
    queues, embeddings_cache, finished_tasks, run_time, start
):
    while True:
        if len(queues["waiting_for_embedding"][1]) > 0:
            payload = queues["waiting_for_embedding"][1].pop()
        else:
            try:
                payload = queues["waiting_for_embedding"][0].get_nowait()
            except Empty:
                break

        if payload["task_name"] in finished_tasks:
            continue
        trace_val = payload["trace_val"]
        if any(v not in embeddings_cache for v in trace_val[0]):
            queues["waiting_for_embedding"][1].append(payload)
            break

        payload["embedding_time"] = run_time
        payload["fetch_time"] += time() - start
        queues["processing_queue"].put(payload)


def embedding_loop(queues, model, model_lock, embeddings_cache, finished_tasks):
    try:
        gpu_mem_threshold = 10**9
        max_batch_size = 128
        pending_payload = None

        while True:
            start = time()
            trace_val_batch = []
            max_value_length = 0
            mem_footprint = 0
            while len(trace_val_batch) < max_batch_size:
                try:
                    if pending_payload:
                        new_payload = pending_payload
                        pending_payload = None
                    else:
                        new_payload = queues["embeddings_queue"].get_nowait()
                    if (
                        new_payload["task_name"] in finished_tasks
                        or new_payload["trace_val"] in embeddings_cache
                    ):
                        continue
                    new_val_max_length = max(
                        max_value_length, len(new_payload["trace_val"])
                    )
                    new_mem_footprint = new_val_max_length**2 * (
                        len(trace_val_batch) + 1
                    )
                    if new_mem_footprint > gpu_mem_threshold:
                        pending_payload = new_payload
                        break
                    trace_val_batch.append(new_payload["trace_val"])
                    max_value_length = new_val_max_length
                    mem_footprint = new_mem_footprint
                except Empty:
                    break
            if not trace_val_batch:
                check_next_embedding_batches(
                    queues, embeddings_cache, finished_tasks, 0.0, start
                )
                sleep(0.001)
                continue

            # print(f"Got embeddings batch")

            with model_lock:
                start_processing = time()
                print(
                    f"Processing embeddings batch {len(trace_val_batch)} {max_value_length} {mem_footprint}"
                )
                trace_val_embedding = model.get_embedding(trace_val_batch).cpu()
                if guiding_model.device == "mps":
                    torch.mps.empty_cache()
                # print("Processed embeddings batch")
                run_time = time() - start_processing

            print(
                f"Processed embeddings batch {len(trace_val_batch)} {max_value_length} {mem_footprint} in {run_time} seconds"
            )

            for i, trace_val in enumerate(trace_val_batch):
                embeddings_cache[trace_val] = trace_val_embedding[i, :].clone()

            wandb.log(
                {
                    "embedding_processing_time": run_time,
                    "embedding_batch_size": len(trace_val_batch),
                    "embedding_batch_max_size": max_value_length,
                    "embedding_batch_mem_footprint": mem_footprint,
                }
            )

            check_next_embedding_batches(
                queues, embeddings_cache, finished_tasks, run_time, start
            )
    finally:
        print("Exiting embedding loop")


def main_processing_loop(
    redis_db,
    queues,
    model,
    model_lock,
    current_grammar,
    embeddings_cache,
    inputs_cache,
    outputs_cache,
    finished_tasks,
):
    try:
        redis_conn = redis.Redis(host="localhost", port=6379, db=redis_db)
        batch_size = 32
        while True:
            start = time()
            payloads = []
            while len(payloads) < batch_size:
                try:
                    new_payload = queues["processing_queue"].get_nowait()
                    if new_payload["task_name"] in finished_tasks:
                        continue
                    payloads.append(new_payload)
                except Empty:
                    break

            if not payloads:
                sleep(0.001)
                continue
            # print("Got processing batch")

            start_processing = time()
            # print(f"Processing batch {len(payloads)}")
            # print(payloads)
            trace_val_batch = torch.stack(
                [
                    embeddings_cache[trace_val]
                    for v in payloads
                    for trace_val in v["trace_val"][0]
                ]
            )
            # print(trace_val_batch.shape)
            trace_val_mask = model.combine_masks([v["trace_val"][1] for v in payloads])
            stacking_time = time() - start_processing
            # print(trace_val_mask.shape)

            with model_lock:
                start_processing = time()
                with torch.no_grad():
                    trace_val_batch = trace_val_batch.to(device)
                    trace_val_mask = model.transfer_to_device(trace_val_mask)
                    trace_val_embedding = torch.matmul(
                        trace_val_batch.H, trace_val_mask
                    ).H
                    # print(trace_val_embedding)
                    # print(trace_val_embedding.shape)
                    input_encodings = torch.stack(
                        [inputs_cache[v["task_name"]] for v in payloads]
                    )
                    # print(input_encodings)
                    # print(input_encodings.shape)
                    output_encodings = torch.stack(
                        [outputs_cache[v["task_name"]] for v in payloads]
                    )
                    is_reversed = model.transfer_to_device(
                        [[v["is_known"]] for v in payloads]
                    )
                    # print(is_reversed.shape)
                    grammar_func_encodings, grammar_encodings = current_grammar[0]
                    result = model.body(
                        grammar_func_encodings,
                        grammar_encodings,
                        input_encodings,
                        output_encodings,
                        trace_val_embedding,
                        is_reversed,
                    ).cpu()
                run_time = time() - start_processing
            # print(result)
            # print(result.shape)

            wandb.log(
                {
                    "processing_stacking_time": stacking_time,
                    "processing_time": run_time,
                    "processing_batch_size": len(payloads),
                }
            )

            for i, payload in enumerate(payloads):
                full_run_time = time() - payload["start_time"]
                out_payload = {
                    "entry_id": payload["entry_id"],
                    "result": result[i, :].tolist(),
                    "is_known": payload["is_known"],
                    "times": {
                        "fetch": payload["fetch_time"] + (time() - start),
                        "processing_stacking": stacking_time,
                        "processing": run_time,
                        "run": full_run_time,
                    },
                }
                if "input_time" in payload:
                    out_payload["times"]["input"] = payload["input_time"]
                    out_payload["times"]["input_preprocessing"] = payload[
                        "input_preprocessing_time"
                    ]
                if "output_time" in payload:
                    out_payload["times"]["output"] = payload["output_time"]
                    out_payload["times"]["output_preprocessing"] = payload[
                        "output_preprocessing_time"
                    ]
                if "embedding_time" in payload:
                    out_payload["times"]["embedding"] = payload["embedding_time"]
                redis_conn.rpush(payload["task_name"], orjson.dumps(out_payload))
            # print("Processed batch")
    finally:
        print("Exiting main processing loop")


def finished_tasks_loop(redis_db, finished_tasks):
    redis_conn = redis.Redis(
        host="localhost", port=6379, db=redis_db, decode_responses=True
    )
    while True:
        task_name = redis_conn.lpop("finished_tasks")
        if not task_name:
            sleep(0.001)
            continue
        finished_tasks.add(task_name)


class EmbeddingsCache(dict):
    max_chunk_size = 1000

    def __init__(self, chunks=None):
        if not chunks:
            self.chunks = [{}]
            self.saved_chunks = 0
        else:
            self.chunks = chunks
            if len(self.chunks[-1]) == self.max_chunk_size:
                self.saved_chunks = len(self.chunks)
            else:
                self.saved_chunks = len(self.chunks) - 1

    def __contains__(self, key):
        result = any(key in chunk for chunk in self.chunks)
        # print("Checking", key, result)
        return result

    def __getitem__(self, key):
        # print("Getting", key)
        for chunk in self.chunks:
            if key in chunk:
                return chunk[key]
        raise KeyError(key)

    def __setitem__(self, key, value):
        # print("Setting", key)
        for chunk in self.chunks:
            if key in chunk:
                return
        else:  # key not found
            if len(self.chunks[-1]) < self.max_chunk_size:
                self.chunks[-1][key] = value
            else:
                self.chunks.append({key: value})

    @classmethod
    def restore_from_path(cls, dir_path):
        start = time()
        chunks = []
        if not os.path.exists(dir_path):
            os.mkdir(dir_path)
        for fname in sorted(os.listdir(dir_path), key=lambda name: int(name[6:-4])):
            with open(os.path.join(dir_path, fname), "rb") as f:
                chunks.append(pickle.load(f))
        result = cls(chunks)
        print(f"Restored embeddings cache in {time() - start} seconds")
        return result

    def save_to_path(self, dir_path):
        start = time()
        chunks_to_save = range(self.saved_chunks, len(self.chunks))
        total_length = 0
        for i in chunks_to_save:
            total_length += len(self.chunks[i])
            with open(os.path.join(dir_path, f"chunk_{i}.pkl"), "wb") as f:
                pickle.dump(self.chunks[i], f)
            if len(self.chunks[i]) == self.max_chunk_size:
                self.saved_chunks = i + 1

        print(
            f"Saved {len(chunks_to_save)} embeddings chunks of total length {total_length} in {time() - start} seconds"
        )


def save_embeddings_cache_loop(embeddings_cache):
    while True:
        sleep(60)
        embeddings_cache.save_to_path("embeddings_cache")


class GuidingRedisDataset(Dataset):
    def __init__(self, redis_db, model, model_lock, payload, embeddings_cache) -> None:
        super().__init__()
        self.redis_db = redis_db
        self.model = model
        self.model_lock = model_lock
        self.size = payload["count"]
        self.redis_key = payload["key"]
        self.embeddings_cache = embeddings_cache
        self.loaded_data = []
        self.loading_thread = Thread(target=self._load_data)
        self.loading_thread.start()

    def __len__(self):
        return self.size

    def _load_data(self):
        redis_conn = redis.Redis(host="localhost", port=6379, db=self.redis_db)
        for i in range(self.size):
            data_str = redis_conn.lpop(self.redis_key)
            # print(data_str)
            data = orjson.loads(data_str)
            # print(data)
            inputs = preprocess_inputs_batch([data])
            outputs = preprocess_outputs_batch([data])

            trace_vals, trace_mask = data["trace_val"]
            new_trace_vals = list(
                set(v for v in trace_vals if v not in self.embeddings_cache)
            )

            if new_trace_vals:
                with self.model_lock:
                    trace_val_embedding = self.model.get_embedding(new_trace_vals).cpu()
                    if guiding_model.device == "mps":
                        torch.mps.empty_cache()

                for i, trace_val in enumerate(new_trace_vals):
                    self.embeddings_cache[trace_val] = trace_val_embedding[i, :]

            trace_mask = np.array(trace_mask)
            is_reversed = data["is_rev"]

            uses, mask, N, constant = data["summary"]
            uses = np.array(uses)
            # print(mask)
            mask = np.transpose(np.array(mask))
            # print(mask)
            N = np.array(N)

            self.loaded_data.append(
                (
                    (inputs, outputs, (trace_vals, trace_mask), is_reversed),
                    (uses, mask, N, constant),
                )
            )

    def __getitem__(self, index):
        while len(self.loaded_data) <= index:
            if not self.loading_thread.is_alive():
                self.loading_thread.join()
            sleep(0.001)
        return index, self.loaded_data[index]


class BatchCombiner:
    def __init__(self, grammar, model, model_lock, embeddings_cache):
        self.grammar = grammar
        self.grammar_enc_cache = None
        self.model = model
        self.model_lock = model_lock
        self.embeddings_cache = embeddings_cache
        self.cache = {}

    def __call__(self, batch):
        if self.grammar_enc_cache is None:
            new_funcs = [f for f in self.grammar if f not in self.embeddings_cache]

            if new_funcs:
                with self.model_lock:
                    new_funcs_embedding = self.model.get_embedding(new_funcs).cpu()
                for i, f in enumerate(new_funcs):
                    self.embeddings_cache[f] = new_funcs_embedding[i, :]

            with self.model_lock:
                grammar_func_encodings = torch.stack(
                    [self.embeddings_cache[f] for f in self.grammar]
                ).to(device)

                grammar_encodings = torch.mean(grammar_func_encodings, dim=0)
            self.grammar_enc_cache = grammar_func_encodings, grammar_encodings

        idx_key = frozenset([x[0] for x in batch])
        if idx_key not in self.cache:
            inputs = self.model.process_input_output_batch([x[1][0][0] for x in batch])
            outputs = self.model.process_input_output_batch([x[1][0][1] for x in batch])
            trace_values = [x[1][0][2] for x in batch]
            all_traces = list(itertools.chain(*[t[0] for t in trace_values]))
            trace_mask = self.model.combine_masks([t[1] for t in trace_values])

            with self.model_lock:
                trace_embiddings = torch.stack(
                    [self.embeddings_cache[t] for t in all_traces]
                ).to(device)
                trace_mask = torch.tensor(trace_mask).to(device)

                trace_val_embedding = torch.matmul(trace_embiddings.H, trace_mask).H

                is_reversed = torch.tensor(
                    [x[1][0][3] for x in batch], dtype=torch.float32, device=device
                ).reshape(-1, 1)

                uses = torch.utils.data.default_collate([x[1][1][0] for x in batch]).to(
                    device, dtype=torch.float32
                )
                mask = [x[1][1][1] for x in batch]
                N = [x[1][1][2] for x in batch]

                max_norm_count = max(len(n) for n in N)
                merged_mask = np.zeros(
                    (len(N), uses.shape[1], max_norm_count), dtype=np.float32
                )
                merged_N = np.zeros((len(N), max_norm_count), dtype=np.float32)
                for i, n in enumerate(N):
                    merged_N[i, : len(n)] = n
                    # print(mask[i])
                    merged_mask[i, :, : len(n)] = mask[i]

                merged_mask = torch.tensor(merged_mask).to(device)
                merged_N = torch.tensor(merged_N).to(device)

                constant = torch.utils.data.default_collate(
                    [x[1][1][3] for x in batch]
                ).to(device, dtype=torch.float32)
            self.cache[idx_key] = (
                (inputs, outputs, trace_val_embedding, is_reversed),
                (uses, merged_mask, merged_N, constant),
            )
        return self.grammar_enc_cache, self.cache[idx_key]


def build_dataset(
    redis_db, model, model_lock, group_payload, embeddings_cache, batch_size
):
    payload = orjson.loads(group_payload)
    return DataLoader(
        GuidingRedisDataset(redis_db, model, model_lock, payload, embeddings_cache),
        batch_size=batch_size,
        collate_fn=BatchCombiner(
            payload["grammar"], model, model_lock, embeddings_cache
        ),
    )


def update_model_loop(redis_db, model, model_lock, embeddings_cache):
    redis_conn = redis.Redis(
        host="localhost", port=6379, db=redis_db, decode_responses=True
    )
    batch_size = 32
    while True:
        update_groups_count = redis_conn.get("update_model")
        if not update_groups_count:
            sleep(0.01)
            continue

        train_set = []
        for i in range(int(update_groups_count)):
            group_payload = redis_conn.lpop("train_set")
            train_set.append(
                build_dataset(
                    redis_db,
                    model,
                    model_lock,
                    group_payload,
                    embeddings_cache,
                    batch_size,
                )
            )
        model.run_training(train_set, model_lock)
        redis_conn.delete("update_model")


def save_model_loop(redis_db, model):
    redis_conn = redis.Redis(
        host="localhost", port=6379, db=redis_db, decode_responses=True
    )
    while True:
        path = redis_conn.get("save_model")
        if not path:
            sleep(0.01)
            continue
        model.save(path)
        redis_conn.delete("save_model")


def load_model_loop(redis_db, model):
    redis_conn = redis.Redis(
        host="localhost", port=6379, db=redis_db, decode_responses=True
    )
    while True:
        path = redis_conn.get("load_model")
        if not path:
            sleep(0.01)
            continue
        model.load(path)
        redis_conn.delete("load_model")


def main():
    print("Starting guiding model server...")
    redis_db = sys.argv[1]
    model = guiding_model.create_model()
    model_lock = Lock()
    current_grammar = [None]
    finished_tasks = set()
    embeddings_cache = EmbeddingsCache.restore_from_path("embeddings_cache")
    queues = {
        "embeddings_queue": SimpleQueue(),
        "inputs_queue": SimpleQueue(),
        "outputs_queue": SimpleQueue(),
        "waiting_for_inputs": (SimpleQueue(), []),
        "waiting_for_outputs": (SimpleQueue(), []),
        "waiting_for_embedding": (SimpleQueue(), []),
        "processing_queue": SimpleQueue(),
    }
    inputs_cache = {}
    outputs_cache = {}

    wandb.init(
        # set the wandb project where this run will be logged
        project="expcoder",
        # track hyperparameters and run metadata
        config={},
    )

    set_grammar_thread = Thread(
        target=current_grammar_loop,
        args=(redis_db, model, model_lock, current_grammar, embeddings_cache),
    )
    set_grammar_thread.start()
    fetch_thread = Thread(
        target=fetching_loop,
        args=(
            redis_db,
            queues,
            embeddings_cache,
            inputs_cache,
            outputs_cache,
            finished_tasks,
        ),
    )
    fetch_thread.start()
    inputs_thread = Thread(
        target=inputs_loop,
        args=(queues, model, model_lock, inputs_cache, finished_tasks),
    )
    inputs_thread.start()
    outputs_thread = Thread(
        target=outputs_loop,
        args=(queues, model, model_lock, outputs_cache, finished_tasks),
    )
    outputs_thread.start()
    emb_thread = Thread(
        target=embedding_loop,
        args=(queues, model, model_lock, embeddings_cache, finished_tasks),
    )
    emb_thread.start()
    finished_tasks_thread = Thread(
        target=finished_tasks_loop, args=(redis_db, finished_tasks)
    )
    finished_tasks_thread.start()
    main_processing_thread = Thread(
        target=main_processing_loop,
        args=(
            redis_db,
            queues,
            model,
            model_lock,
            current_grammar,
            embeddings_cache,
            inputs_cache,
            outputs_cache,
            finished_tasks,
        ),
    )
    main_processing_thread.start()
    save_embeddings_cache_thread = Thread(
        target=save_embeddings_cache_loop, args=(embeddings_cache,)
    )
    save_embeddings_cache_thread.start()
    update_model_thread = Thread(
        target=update_model_loop, args=(redis_db, model, model_lock, embeddings_cache)
    )
    update_model_thread.start()
    save_model_thread = Thread(target=save_model_loop, args=(redis_db, model))
    save_model_thread.start()
    load_model_thread = Thread(target=load_model_loop, args=(redis_db, model))
    load_model_thread.start()


if __name__ == "__main__":
    main()
