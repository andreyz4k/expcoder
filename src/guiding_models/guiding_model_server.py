import itertools
import os
from collections import OrderedDict, deque
from queue import Empty, SimpleQueue
from threading import Event, Lock, Thread
from time import sleep, time
import sys
import traceback
import numpy as np
import redis
import orjson
import torch
from torch.utils.data import DataLoader, Dataset
import wandb


from embeddings_cache import SQLiteEmbeddingsCache, RedisEmbeddingsCache
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
            embeddings_cache.set_many(
                {f: new_funcs_embedding[i, :] for i, f in enumerate(new_funcs)}
            )

        with model_lock:
            grammar_func_encodings = torch.stack(
                embeddings_cache.get_batch(new_grammar)
            ).to(device)

            grammar_encodings = torch.mean(grammar_func_encodings, dim=0)

        current_grammar[0] = grammar_func_encodings, grammar_encodings
        redis_conn.delete("set_current_grammar")


class PerTaskQueue:
    """FIFO queues per task, served round-robin across tasks.

    Dropping a finished task removes all of its items at once.
    """

    def __init__(self):
        self.lock = Lock()
        self.queues = OrderedDict()
        self.size = 0

    def put(self, task_name, item):
        with self.lock:
            q = self.queues.get(task_name)
            if q is None:
                q = self.queues[task_name] = deque()
            q.append(item)
            self.size += 1

    def get_batch(self, max_items):
        items = []
        with self.lock:
            while len(items) < max_items and self.queues:
                task_name, q = next(iter(self.queues.items()))
                items.append(q.popleft())
                self.size -= 1
                if q:
                    self.queues.move_to_end(task_name)
                else:
                    del self.queues[task_name]
        return items

    def drop_task(self, task_name):
        with self.lock:
            q = self.queues.pop(task_name, None)
            if q is not None:
                self.size -= len(q)

    def __len__(self):
        return self.size


class DependencyTracker:
    """Requests waiting for task inputs/outputs encodings or trace value embeddings.

    Dependency keys are ("inputs", task_name), ("outputs", task_name) and ("emb", value).
    A request goes to the processing queue as soon as all of its own dependencies are
    resolved, so a request waiting on a slow embedding doesn't block other requests.
    """

    def __init__(self, processing_queue):
        self.lock = Lock()
        self.processing_queue = processing_queue
        self.waiters = {}  # dependency key -> set of request ids
        self.pending = {}  # request id -> (payload, set of missing keys)
        self.by_task = {}  # task name -> set of request ids
        self.next_id = 0

    def add(self, payload, missing):
        if not missing:
            self.processing_queue.put(payload["task_name"], payload)
            return
        with self.lock:
            request_id = self.next_id
            self.next_id += 1
            self.pending[request_id] = (payload, set(missing))
            self.by_task.setdefault(payload["task_name"], set()).add(request_id)
            for key in missing:
                self.waiters.setdefault(key, set()).add(request_id)

    def resolve(self, keys, times=None):
        ready = []
        with self.lock:
            for key in keys:
                for request_id in self.waiters.pop(key, ()):
                    payload, missing = self.pending[request_id]
                    missing.discard(key)
                    if times:
                        payload.update(times)
                    if not missing:
                        del self.pending[request_id]
                        task_ids = self.by_task[payload["task_name"]]
                        task_ids.discard(request_id)
                        if not task_ids:
                            del self.by_task[payload["task_name"]]
                        ready.append(payload)
        for payload in ready:
            self.processing_queue.put(payload["task_name"], payload)

    def has_waiters(self, key):
        with self.lock:
            return key in self.waiters

    def drop_task(self, task_name):
        with self.lock:
            for request_id in self.by_task.pop(task_name, ()):
                _, missing = self.pending.pop(request_id)
                for key in missing:
                    key_waiters = self.waiters.get(key)
                    if key_waiters is not None:
                        key_waiters.discard(request_id)
                        if not key_waiters:
                            del self.waiters[key]

    def __len__(self):
        return len(self.pending)


class PipelineState:
    def __init__(self, embeddings_cache):
        self.embeddings_cache = embeddings_cache
        self.inputs_cache = {}
        self.outputs_cache = {}
        self.finished_tasks = set()
        self.inputs_queue = SimpleQueue()
        self.outputs_queue = SimpleQueue()
        self.embeddings_queue = PerTaskQueue()
        self.processing_queue = PerTaskQueue()
        self.waiting = DependencyTracker(self.processing_queue)
        # Set while the main processing loop waits for the model lock
        self.processing_wants_lock = Event()

    def is_available(self, key):
        kind, value = key
        if kind == "emb":
            return value in self.embeddings_cache
        if kind == "inputs":
            return value in self.inputs_cache
        return value in self.outputs_cache

    def backlog_size(self):
        return len(self.processing_queue) + len(self.waiting)

    def drop_task(self, task_name):
        self.finished_tasks.add(task_name)
        self.processing_queue.drop_task(task_name)
        self.embeddings_queue.drop_task(task_name)
        self.waiting.drop_task(task_name)
        self.inputs_cache.pop(task_name, None)
        self.outputs_cache.pop(task_name, None)


def process_request(payload, state):
    start = time()
    task_name = payload["task_name"]

    missing = [
        ("emb", v) for v in set(payload["trace_val"][0]) if v not in state.embeddings_cache
    ]
    # Inputs and outputs encodings are requested once, when the task is registered
    if task_name not in state.outputs_cache:
        missing.append(("outputs", task_name))
    if task_name not in state.inputs_cache:
        missing.append(("inputs", task_name))

    payload["start_time"] = start
    payload["fetch_time"] = time() - start
    state.waiting.add(payload, missing)

    if missing:
        # A dependency could have been resolved between the check above and the
        # registration, in which case nobody would resolve it for this request
        resolved = [key for key in missing if state.is_available(key)]
        if resolved:
            state.waiting.resolve(resolved)
        for kind, value in missing:
            if kind == "emb" and ("emb", value) not in resolved:
                state.embeddings_queue.put(
                    task_name, {"task_name": task_name, "trace_val": value}
                )


def register_task(redis_conn, task_name, state):
    task_io_str = redis_conn.get(f"task_io:{task_name}")
    if not task_io_str:
        # The task has already finished
        return False
    task_io = orjson.loads(task_io_str)
    if task_name not in state.outputs_cache:
        state.outputs_queue.put({"task_name": task_name, "output": task_io["output"]})
    if task_name not in state.inputs_cache:
        state.inputs_queue.put({"task_name": task_name, "inputs": task_io["inputs"]})
    return True


def fetching_iteration(
    redis_conn, state, registered_tasks, per_task_batch, max_backlog
):
    # Keep the backlog in redis, where requests are split by task and dropped
    # in one call when the task finishes
    if state.backlog_size() >= max_backlog:
        sleep(0.001)
        return

    active_tasks = {t.decode() for t in redis_conn.smembers("active_tasks")}

    for task_name in registered_tasks - active_tasks:
        state.drop_task(task_name)
        registered_tasks.discard(task_name)

    for task_name in active_tasks - registered_tasks:
        if task_name in state.finished_tasks:
            continue
        if register_task(redis_conn, task_name, state):
            registered_tasks.add(task_name)

    tasks = [t for t in registered_tasks if t not in state.finished_tasks]
    if not tasks:
        sleep(0.001)
        return
    # Round-robin: every active task gets up to per_task_batch requests per iteration
    pipe = redis_conn.pipeline(transaction=False)
    for task_name in tasks:
        pipe.lpop(f"requests:{task_name}", per_task_batch)
    results = pipe.execute()

    got_any = False
    for task_name, payload_strs in zip(tasks, results):
        if not payload_strs:
            continue
        got_any = True
        for payload_str in payload_strs:
            payload = orjson.loads(payload_str)
            payload["task_name"] = task_name
            process_request(payload, state)
    if not got_any:
        sleep(0.001)


def fetching_loop(redis_db, state):
    redis_conn = redis.Redis(host="localhost", port=6379, db=redis_db)
    registered_tasks = set()
    per_task_batch = 16
    max_backlog = 2048
    while True:
        fetching_iteration(
            redis_conn, state, registered_tasks, per_task_batch, max_backlog
        )


def preprocess_inputs_entry(inputs_entry):
    input_grids = [
        [np.array(example) for example in var] for var in inputs_entry["inputs"]
    ]

    example_count = sum(len(var) for var in input_grids)
    combined_batch = []
    subbatch_mask = np.zeros((example_count, 1), dtype=np.float32)

    m = 0
    for k, var in enumerate(input_grids):
        for example in var:
            combined_batch.append(example)
        subbatch_mask[m : m + len(var), k] = 1 / (len(var) * len(input_grids))
        m += len(var)

    return combined_batch, subbatch_mask


def preprocess_outputs_entry(outputs_entry):
    output_grids = [np.array(example) for example in outputs_entry["output"]]

    example_count = len(output_grids)

    subbatch_mask = np.repeat(1 / example_count, example_count).reshape(
        (example_count, 1)
    )

    return output_grids, subbatch_mask


def task_io_iteration(state, model, model_lock, kind, batch_size):
    if kind == "inputs":
        queue, cache, preprocess = (
            state.inputs_queue,
            state.inputs_cache,
            preprocess_inputs_entry,
        )
    else:
        queue, cache, preprocess = (
            state.outputs_queue,
            state.outputs_cache,
            preprocess_outputs_entry,
        )
    batch = []
    task_names = set()
    while len(batch) < batch_size:
        try:
            new_payload = queue.get_nowait()
        except Empty:
            break
        task_name = new_payload["task_name"]
        if (
            task_name in state.finished_tasks
            or task_name in task_names
            or task_name in cache
        ):
            continue
        task_names.add(task_name)
        batch.append(new_payload)
    if not batch:
        sleep(0.001)
        return

    start_processing = time()
    combined_batch = [preprocess(entry) for entry in batch]
    preprocessing_time = time() - start_processing

    with model_lock:
        start_processing = time()
        combined_batch = model.process_input_output_batch(combined_batch)
        with torch.no_grad():
            encodings = model.input_output_encoder(*combined_batch)
        processing_time = time() - start_processing

    for i, v in enumerate(batch):
        if v["task_name"] not in state.finished_tasks:
            cache[v["task_name"]] = encodings[i, :]

    prefix = "input" if kind == "inputs" else "output"
    wandb.log(
        {
            f"{kind}_processing_time": processing_time,
            f"{kind}_preprocessing_time": preprocessing_time,
            f"{kind}_batch_size": len(batch),
        }
    )
    state.waiting.resolve(
        [(kind, v["task_name"]) for v in batch],
        {
            f"{prefix}_time": processing_time,
            f"{prefix}_preprocessing_time": preprocessing_time,
        },
    )


def task_io_loop(state, model, model_lock, kind):
    try:
        batch_size = 32
        while True:
            task_io_iteration(state, model, model_lock, kind, batch_size)
    finally:
        print(f"Exiting {kind} loop")


class EmbeddingBatcher:
    """Trace values waiting to be embedded, grouped into batches of similar length.

    Each batch is padded to its longest value, so mixing short and long values wastes
    most of the compute on padding. Values are tokenized when they enter the pool and
    batches are cut by a budget of padded tokens. The shortest values go first, unless
    a value has been waiting longer than max_wait, so long values aren't starved.
    """

    def __init__(
        self,
        max_pool_size=1024,
        max_batch_size=128,
        token_budget=8192,
        attention_budget=2**24,
        max_wait=5.0,
    ):
        self.pool = {}  # value -> (token ids, time it entered the pool)
        self.max_pool_size = max_pool_size
        self.max_batch_size = max_batch_size
        self.token_budget = token_budget
        self.attention_budget = attention_budget
        self.max_wait = max_wait

    def refill(self, state, model):
        new_values = []
        new_values_set = set()
        while len(self.pool) + len(new_values) < self.max_pool_size:
            items = state.embeddings_queue.get_batch(
                min(64, self.max_pool_size - len(self.pool) - len(new_values))
            )
            if not items:
                break
            for item in items:
                value = item["trace_val"]
                if (
                    item["task_name"] in state.finished_tasks
                    or value in self.pool
                    or value in new_values_set
                    or not state.waiting.has_waiters(("emb", value))
                ):
                    continue
                new_values.append(value)
                new_values_set.add(value)
        if not new_values:
            return
        # Checked once per value when it enters the pool, this is a SQLite query
        cached = [v for v in new_values if v in state.embeddings_cache]
        if cached:
            state.waiting.resolve([("emb", v) for v in cached])
            new_values = [v for v in new_values if v not in set(cached)]
        if not new_values:
            return
        now = time()
        for value, token_ids in zip(new_values, model.embedder.tokenize(new_values)):
            self.pool[value] = (token_ids, now)

    def drop_unneeded(self, state):
        for value in list(self.pool):
            if not state.waiting.has_waiters(("emb", value)):
                del self.pool[value]

    def _fits(self, count, max_length):
        return (
            count * max_length <= self.token_budget
            and count * max_length**2 <= self.attention_budget
        )

    def next_batch(self):
        if not self.pool:
            return []
        order = sorted(self.pool, key=lambda v: len(self.pool[v][0]))
        oldest = min(self.pool, key=lambda v: self.pool[v][1])
        if time() - self.pool[oldest][1] > self.max_wait:
            anchor = order.index(oldest)
        else:
            anchor = 0
        batch = [order[anchor]]
        max_length = len(self.pool[order[anchor]][0])
        # Shorter values fit under the anchor's padded length
        i = anchor - 1
        while (
            i >= 0
            and len(batch) < self.max_batch_size
            and self._fits(len(batch) + 1, max_length)
        ):
            batch.append(order[i])
            i -= 1
        i = anchor + 1
        while i < len(order) and len(batch) < self.max_batch_size:
            length = len(self.pool[order[i]][0])
            if not self._fits(len(batch) + 1, length):
                break
            batch.append(order[i])
            max_length = length
            i += 1
        return batch

    def take(self, batch):
        token_ids = [self.pool.pop(v)[0] for v in batch]
        return token_ids


def wait_for_processing_turn(state, max_wait=0.05):
    # Main processing batches take milliseconds, while an embedding batch can take
    # seconds and would make every worker wait, so let processing go first
    start = time()
    while (
        state.processing_wants_lock.is_set() or len(state.processing_queue) > 0
    ) and time() - start < max_wait:
        sleep(0.001)


def embedding_iteration(state, batcher, model, model_lock, empty_mps_cache):
    batcher.refill(state, model)
    batcher.drop_unneeded(state)
    batch = batcher.next_batch()
    if not batch:
        sleep(0.001)
        return
    token_ids = batcher.take(batch)
    max_tokens = max(len(t) for t in token_ids)
    real_tokens = sum(len(t) for t in token_ids)
    padded_tokens = max_tokens * len(token_ids)

    wait_for_processing_turn(state)
    with model_lock:
        start_processing = time()
        trace_val_embedding = model.get_embedding_from_tokens(token_ids).cpu()
        if empty_mps_cache and guiding_model.device == "mps":
            torch.mps.empty_cache()
        run_time = time() - start_processing

    print(
        f"Processed embeddings batch {len(batch)} {max_tokens} tokens "
        f"({real_tokens}/{padded_tokens} not padding) in {run_time} seconds"
    )

    state.embeddings_cache.set_many(
        {
            trace_val: trace_val_embedding[i, :].clone()
            for i, trace_val in enumerate(batch)
        }
    )

    wandb.log(
        {
            "embedding_processing_time": run_time,
            "embedding_batch_size": len(batch),
            "embedding_batch_max_tokens": max_tokens,
            "embedding_batch_padded_tokens": padded_tokens,
            "embedding_batch_useful_fraction": real_tokens / padded_tokens,
            "embedding_pool_size": len(batcher.pool),
        }
    )

    state.waiting.resolve([("emb", v) for v in batch], {"embedding_time": run_time})


def embedding_loop(state, model, model_lock):
    try:
        batcher = EmbeddingBatcher()
        empty_mps_cache = os.environ.get("EXPCODER_MPS_EMPTY_CACHE", "1") == "1"
        while True:
            embedding_iteration(state, batcher, model, model_lock, empty_mps_cache)
    finally:
        print("Exiting embedding loop")


def main_processing_iteration(
    redis_conn, state, model, model_lock, current_grammar, batch_size
):
    start = time()
    payloads = []
    input_encodings = []
    output_encodings = []
    for payload in state.processing_queue.get_batch(batch_size):
        task_name = payload["task_name"]
        if task_name in state.finished_tasks:
            continue
        input_encoding = state.inputs_cache.get(task_name)
        output_encoding = state.outputs_cache.get(task_name)
        if input_encoding is None or output_encoding is None:
            # The task was dropped in the meantime
            continue
        payloads.append(payload)
        input_encodings.append(input_encoding)
        output_encodings.append(output_encoding)

    if not payloads:
        sleep(0.001)
        return

    start_processing = time()
    trace_val_batch = torch.stack(
        state.embeddings_cache.get_batch(
            [trace_val for v in payloads for trace_val in v["trace_val"][0]]
        )
    )
    trace_val_mask = model.combine_masks([v["trace_val"][1] for v in payloads])
    stacking_time = time() - start_processing

    # Tells the embedding loop to let this batch go first
    state.processing_wants_lock.set()
    with model_lock:
        state.processing_wants_lock.clear()
        start_processing = time()
        with torch.no_grad():
            trace_val_batch = trace_val_batch.to(device)
            trace_val_mask = model.transfer_to_device(trace_val_mask)
            trace_val_embedding = torch.matmul(trace_val_batch.H, trace_val_mask).H
            input_encodings = torch.stack(input_encodings)
            output_encodings = torch.stack(output_encodings)
            is_reversed = model.transfer_to_device([[v["is_known"]] for v in payloads])
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

    wandb.log(
        {
            "processing_stacking_time": stacking_time,
            "processing_time": run_time,
            "processing_batch_size": len(payloads),
        }
    )

    pipe = redis_conn.pipeline(transaction=False)
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
        pipe.rpush(payload["task_name"], orjson.dumps(out_payload))
    pipe.execute()


def main_processing_loop(redis_db, state, model, model_lock, current_grammar):
    try:
        redis_conn = redis.Redis(host="localhost", port=6379, db=redis_db)
        batch_size = 128
        while True:
            main_processing_iteration(
                redis_conn, state, model, model_lock, current_grammar, batch_size
            )
    finally:
        print("Exiting main processing loop")


def finished_tasks_loop(redis_db, state):
    redis_conn = redis.Redis(
        host="localhost", port=6379, db=redis_db, decode_responses=True
    )
    while True:
        task_name = redis_conn.lpop("finished_tasks")
        if not task_name:
            sleep(0.001)
            continue
        state.drop_task(task_name)


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
            inputs = preprocess_inputs_entry(data)
            outputs = preprocess_outputs_entry(data)

            trace_vals, trace_mask = data["trace_val"]
            new_trace_vals = list(
                set(v for v in trace_vals if v not in self.embeddings_cache)
            )

            if new_trace_vals:
                with self.model_lock:
                    trace_val_embedding = self.model.get_embedding(new_trace_vals).cpu()
                    if guiding_model.device == "mps":
                        torch.mps.empty_cache()

                self.embeddings_cache.set_many(
                    {
                        trace_val: trace_val_embedding[i, :].clone()
                        for i, trace_val in enumerate(new_trace_vals)
                    }
                )

            trace_mask = np.array(trace_mask)
            is_reversed = data["is_rev"]

            uses, norm_sets, N, constant = data["summary"]
            uses = np.array(uses)
            N = np.array(N)

            self.loaded_data.append(
                (
                    (inputs, outputs, (trace_vals, trace_mask), is_reversed),
                    (uses, norm_sets, N, constant),
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
                self.embeddings_cache.set_many(
                    {
                        f: new_funcs_embedding[i, :].clone()
                        for i, f in enumerate(new_funcs)
                    }
                )

            with self.model_lock:
                grammar_func_encodings = torch.stack(
                    self.embeddings_cache.get_batch(self.grammar)
                ).to(device)

                grammar_encodings = torch.mean(grammar_func_encodings, dim=0)
            self.grammar_enc_cache = grammar_func_encodings, grammar_encodings

        idx_key = frozenset([x[0] for x in batch])
        if idx_key not in self.cache:
            trace_values = [x[1][0][2] for x in batch]
            all_traces = list(itertools.chain(*[t[0] for t in trace_values]))
            trace_mask = self.model.combine_masks([t[1] for t in trace_values])

            with self.model_lock:
                # process_input_output_batch creates MPS tensors, so it must hold the lock
                inputs = self.model.process_input_output_batch(
                    [x[1][0][0] for x in batch]
                )
                outputs = self.model.process_input_output_batch(
                    [x[1][0][1] for x in batch]
                )
                trace_embiddings = torch.stack(
                    self.embeddings_cache.get_batch(all_traces)
                ).to(device)
                trace_mask = torch.tensor(trace_mask).to(device)

                trace_val_embedding = torch.matmul(trace_embiddings.H, trace_mask).H

                is_reversed = torch.tensor(
                    [x[1][0][3] for x in batch], dtype=torch.float32, device=device
                ).reshape(-1, 1)

                uses = torch.utils.data.default_collate([x[1][1][0] for x in batch]).to(
                    device, dtype=torch.float32
                )
                norm_sets = [x[1][1][1] for x in batch]
                N = [x[1][1][2] for x in batch]

                max_norm_count = max(len(n) for n in N)
                # Padding columns stay 0 (not -inf): their N is 0, and a finite z
                # avoids 0 * -inf = nan in the loss.
                merged_mask = np.zeros(
                    (len(N), uses.shape[1], max_norm_count), dtype=np.float32
                )
                merged_N = np.zeros((len(N), max_norm_count), dtype=np.float32)
                for i, n in enumerate(N):
                    merged_N[i, : len(n)] = n
                    merged_mask[i, :, : len(n)] = -np.inf
                    for j, idxs in enumerate(norm_sets[i]):
                        merged_mask[i, np.asarray(idxs, dtype=np.intp), j] = 0

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
    if device == "mps":
        batch_size = 32
    else:
        batch_size = 64
    while True:
        update_groups_count = redis_conn.get("update_model")
        if not update_groups_count:
            sleep(0.01)
            continue

        train_set = []
        try:
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
        except Exception as e:
            traceback.print_exc()
        finally:
            redis_conn.delete("update_model")


def save_model_loop(redis_db, model, model_lock):
    redis_conn = redis.Redis(
        host="localhost", port=6379, db=redis_db, decode_responses=True
    )
    while True:
        path = redis_conn.get("save_model")
        if not path:
            sleep(0.01)
            continue
        with model_lock:
            model.save(path)
        redis_conn.delete("save_model")


def load_model_loop(redis_db, model, model_lock):
    redis_conn = redis.Redis(
        host="localhost", port=6379, db=redis_db, decode_responses=True
    )
    while True:
        path = redis_conn.get("load_model")
        if not path:
            sleep(0.01)
            continue
        with model_lock:
            model.load(path)
        redis_conn.delete("load_model")


def wandb_logs_loop(redis_db):
    redis_conn = redis.Redis(
        host="localhost", port=6379, db=redis_db, decode_responses=True
    )
    while True:
        config_str = redis_conn.lpop("wandb_config")
        if config_str:
            config_dict = orjson.loads(config_str)
            wandb.config.update(config_dict)
        log_str = redis_conn.lpop("wandb_logs")
        if not log_str:
            sleep(0.001)
            continue
        log_dict = orjson.loads(log_str)
        parsed_log_dict = {}
        for k, v in log_dict.items():
            if isinstance(v, dict) and "type" in v and v["type"] == "table":
                parsed_log_dict[k] = wandb.Table(data=v["data"], columns=v["columns"])
            else:
                parsed_log_dict[k] = v
        wandb.log(parsed_log_dict)


def main():
    print("Starting guiding model server...")
    redis_db = sys.argv[1]
    cache_type = sys.argv[2]
    model = guiding_model.create_model()

    model_lock = Lock()

    load_model_thread = Thread(
        target=load_model_loop, args=(redis_db, model, model_lock)
    )
    load_model_thread.start()

    current_grammar = [None]

    wandb.init(
        # set the wandb project where this run will be logged
        project="expcoder",
        # track hyperparameters and run metadata
        config={},
    )

    if cache_type == "sqlite":
        embeddings_cache = SQLiteEmbeddingsCache("embeddings_cache.db")
    else:
        embeddings_cache = RedisEmbeddingsCache(redis_db)

    print(f"Cache size is {embeddings_cache.get_size()}")
    state = PipelineState(embeddings_cache)

    set_grammar_thread = Thread(
        target=current_grammar_loop,
        args=(redis_db, model, model_lock, current_grammar, embeddings_cache),
    )
    set_grammar_thread.start()
    fetch_thread = Thread(target=fetching_loop, args=(redis_db, state))
    fetch_thread.start()
    inputs_thread = Thread(
        target=task_io_loop, args=(state, model, model_lock, "inputs")
    )
    inputs_thread.start()
    outputs_thread = Thread(
        target=task_io_loop, args=(state, model, model_lock, "outputs")
    )
    outputs_thread.start()
    emb_thread = Thread(target=embedding_loop, args=(state, model, model_lock))
    emb_thread.start()
    finished_tasks_thread = Thread(target=finished_tasks_loop, args=(redis_db, state))
    finished_tasks_thread.start()
    main_processing_thread = Thread(
        target=main_processing_loop,
        args=(redis_db, state, model, model_lock, current_grammar),
    )
    main_processing_thread.start()
    update_model_thread = Thread(
        target=update_model_loop, args=(redis_db, model, model_lock, embeddings_cache)
    )
    update_model_thread.start()
    save_model_thread = Thread(
        target=save_model_loop, args=(redis_db, model, model_lock)
    )
    save_model_thread.start()
    wandb_logs_thread = Thread(target=wandb_logs_loop, args=(redis_db,))
    wandb_logs_thread.start()


if __name__ == "__main__":
    main()
