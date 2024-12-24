from datetime import datetime
import itertools
import math
import os
from threading import Lock
from time import time
import torch.utils
import torch.mps
from tqdm import tqdm
from transformers import AutoModel
from torch import nn
from torch.utils.data import DataLoader, Dataset
import torch
import numpy as np
import wandb

d_emb = 768
d_state_in = d_emb * 4 + 1
d_state_h = 512
d_state_out = 512
d_dec_h = 512
d_dec_h2 = 256

hidden_channels = 32

device = (
    "cuda"
    if torch.cuda.is_available()
    else "mps" if torch.backends.mps.is_available() else "cpu"
)


class InputOutputEncoder(nn.Module):
    def __init__(self):
        super(InputOutputEncoder, self).__init__()
        self.convs = nn.ModuleList(
            [
                nn.Conv2d(10, hidden_channels, kernel_size=(3, 3), padding=1),
                nn.Conv2d(
                    hidden_channels, hidden_channels * 2, kernel_size=(3, 3), padding=1
                ),
                nn.Conv2d(
                    hidden_channels * 2, int(d_emb / 2), kernel_size=(3, 3), padding=1
                ),
                nn.Conv2d(int(d_emb / 2), d_emb, kernel_size=(3, 3), padding=1),
            ]
        )
        self.linear1 = nn.Linear(d_emb, d_emb)
        self.linear2 = nn.Linear(d_emb, d_emb)
        self.pooler = nn.AdaptiveAvgPool2d((1, 1))
        self.activation = nn.ELU()

    def forward(self, inputs, mask, subbatch_mask):
        val = inputs
        for conv in self.convs:
            val = conv(val)
            val = self.activation(val)

            val = torch.mul(val, mask)

        pooled = torch.mean(val, dim=(2, 3))
        l1 = self.linear1(pooled)

        batched = torch.matmul(l1.H, subbatch_mask).H
        return self.linear2(batched)


class GuidingDataset(Dataset):
    def __init__(self, X_data, summaries):
        self.X_data = X_data
        self.summaries = summaries

    def __len__(self):
        return len(self.X_data)

    def __getitem__(self, idx):
        return (idx, self.X_data[idx], self.summaries[idx])


class Combiner:
    def __init__(self, grammar, model):
        self.grammar = grammar
        self.model = model
        self.grammar_enc_cache = None
        self.cache = {}

    def __call__(self, batch):
        if self.grammar_enc_cache is None:
            grammar_func_encodings = self.model.get_embedding(self.grammar)
            grammar_encodings = torch.mean(grammar_func_encodings, dim=0)
            self.grammar_enc_cache = grammar_func_encodings, grammar_encodings

        idx_key = frozenset([x[0] for x in batch])
        if idx_key not in self.cache:
            inputs = self.model.process_input_output_batch([x[1][0] for x in batch])
            outputs = self.model.process_input_output_batch([x[1][1] for x in batch])
            trace_values = [x[1][2] for x in batch]
            all_traces = list(itertools.chain(*[t[0] for t in trace_values]))
            trace_mask = self.model.combine_masks([t[1] for t in trace_values])
            trace_val_embedding = self.model.get_trace_val_embedding(
                all_traces, trace_mask
            )

            is_reversed = torch.tensor(
                [x[1][3] for x in batch], dtype=torch.float32, device=device
            ).reshape(-1, 1)

            uses = torch.utils.data.default_collate([x[2][0] for x in batch]).to(device)
            mask = [x[2][1] for x in batch]
            N = [x[2][2] for x in batch]

            max_norm_count = max(len(n) for n in N)
            merged_mask = np.zeros(
                (len(N), uses.shape[1], max_norm_count), dtype=np.float32
            )
            merged_N = np.zeros((len(N), max_norm_count), dtype=np.float32)
            for i, n in enumerate(N):
                merged_N[i, : len(n)] = n
                merged_mask[i, :, : len(n)] = mask[i]

            merged_mask = torch.tensor(merged_mask).to(device)
            merged_N = torch.tensor(merged_N).to(device)

            constant = torch.utils.data.default_collate([x[2][3] for x in batch]).to(
                device, dtype=torch.float32
            )
            self.cache[idx_key] = (
                (inputs, outputs, trace_val_embedding, is_reversed),
                (uses, merged_mask, merged_N, constant),
            )
        return self.grammar_enc_cache, self.cache[idx_key]


class Embedder:
    def __init__(self) -> None:
        self.model = AutoModel.from_pretrained(
            "jinaai/jina-embeddings-v2-base-code", trust_remote_code=True
        ).to(device)
        self.model.requires_grad_(False)

    def encode(self, batch):
        with torch.no_grad():
            return self.model.encode(batch, convert_to_tensor=True).detach()


class GuidingModelBody(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.state_processor = nn.Sequential(
            nn.Linear(d_state_in, d_state_h),
            nn.ELU(),
            nn.Linear(d_state_h, d_state_h),
            nn.ELU(),
            nn.Linear(d_state_h, d_state_h),
            nn.ELU(),
            nn.Linear(d_state_h, d_state_out),
            nn.ELU(),
        )
        self.decoder = nn.Sequential(
            nn.Linear(d_state_out + d_emb, d_dec_h),
            nn.ELU(),
            nn.Linear(d_dec_h, d_dec_h),
            nn.ELU(),
            nn.Linear(d_dec_h, d_dec_h2),
            nn.ELU(),
            nn.Linear(d_dec_h2, 1),
        )

    def forward(
        self,
        grammar_func_encodings,
        grammar_encodings,
        input_encodings,
        output_encodings,
        trace_val_embedding,
        is_reversed,
    ):
        state_embedding = torch.cat(
            [
                torch.tile(grammar_encodings, (input_encodings.shape[0], 1)),
                input_encodings,
                output_encodings,
                trace_val_embedding,
                is_reversed,
            ],
            dim=1,
        )
        state = self.state_processor(state_embedding)

        broadcasted_state = torch.tile(
            state, (grammar_func_encodings.shape[0], 1, 1)
        ).permute(1, 0, 2)
        broadcasted_f_emb = torch.tile(grammar_func_encodings, (state.shape[0], 1, 1))
        result = self.decoder(
            torch.cat([broadcasted_state, broadcasted_f_emb], dim=2)
        ).squeeze(2)
        return result


class GuidingModel(nn.Module):
    def __init__(self):
        super(GuidingModel, self).__init__()
        self.embedder = Embedder()

        self.input_output_encoder = InputOutputEncoder()
        self.body = GuidingModelBody()

        self.grammar_cache = None
        self.inputs_cache = {}
        self.outputs_cache = {}

    def set_current_grammar(self, grammar):
        grammar_func_encodings = self.get_embedding(grammar)
        grammar_encodings = torch.mean(grammar_func_encodings, dim=0).detach()
        self.grammar_cache = grammar_func_encodings, grammar_encodings

    def get_embedding(self, batch):
        return self.embedder.encode(batch)

    def get_trace_val_embedding(self, trace_val_batch, trace_val_mask):
        trace_val_embedding = self.get_embedding(trace_val_batch)
        trace_val_mask = torch.tensor(trace_val_mask).to(device)

        result = torch.matmul(trace_val_embedding.H, trace_val_mask).H
        return result

    def process_input_output_batch(self, batch):
        batch_size = len(batch)
        example_count = sum(len(m[2]) for m in batch)

        result_subbatch_mask = np.zeros((example_count, batch_size), dtype=np.float32)

        max_x = max(max(v.shape[2] for (v, _, _) in batch), 3)
        max_y = max(max(v.shape[3] for (v, _, _) in batch), 3)
        result_batch_matrix = np.zeros(
            (example_count, 10, max_x, max_y), dtype=np.float32
        )
        result_batch_mask = np.zeros((example_count, 1, max_x, max_y), dtype=np.float32)

        i = 0
        for j, (matrix, mask, subbatch_mask) in enumerate(batch):
            result_subbatch_mask[i : i + len(subbatch_mask), j : j + 1] = subbatch_mask
            result_batch_matrix[
                i : i + len(subbatch_mask),
                :,
                0 : matrix.shape[2],
                0 : matrix.shape[3],
            ] = matrix
            result_batch_mask[
                i : i + len(subbatch_mask),
                :,
                0 : matrix.shape[2],
                0 : matrix.shape[3],
            ] = mask
            i += len(subbatch_mask)
        return (
            torch.tensor(result_batch_matrix, dtype=torch.float32, device=device),
            torch.tensor(result_batch_mask, dtype=torch.float32, device=device),
            torch.tensor(result_subbatch_mask, dtype=torch.float32, device=device),
        )

    def combine_masks(self, masks):
        next_count = sum(max(len(m), 1) for m in masks)
        next_mask = np.zeros((next_count, len(masks)), dtype=np.float32)

        i = 0
        for j, m in enumerate(masks):
            if len(m) == 0:
                next_mask[i, j] = 1
                i += 1
            else:
                next_mask[i : i + len(m), j] = m
                i += len(m)
        return next_mask

    def forward(
        self,
        grammar_func_encodings,
        grammar_encodings,
        inputs_batch: tuple[torch.Tensor, torch.Tensor, torch.Tensor],
        outputs_batch: tuple[torch.Tensor, torch.Tensor, torch.Tensor],
        trace_val_embedding,
        is_reversed,
    ):
        input_encodings = self.input_output_encoder(*inputs_batch)
        output_encodings = self.input_output_encoder(*outputs_batch)
        result = self.body(
            grammar_func_encodings,
            grammar_encodings,
            input_encodings,
            output_encodings,
            trace_val_embedding,
            is_reversed,
        )
        return result

    @staticmethod
    def transfer_to_device(value):
        if isinstance(value, tuple):
            return tuple([torch.tensor(x).to(device) for x in value])
        return torch.tensor(value).to(device)

    def predict(self, inputs_batch, outputs_batch, trace_val_batch, is_reversed):
        try:
            self.eval()
            times = {}
            with torch.no_grad():
                start = time()
                trace_val_embedding = self.get_trace_val_embedding(*trace_val_batch)
                times["trace_val_embedding"] = time() - start

                # inputs_batch = self.transfer_to_device(inputs_batch)
                # outputs_batch = self.transfer_to_device(outputs_batch)
                start = time()
                is_reversed = self.transfer_to_device(is_reversed)
                times["transfer"] = time() - start

                start = time()
                grammar_func_encodings, grammar_encodings = self.grammar_cache
                result = self(
                    grammar_func_encodings,
                    grammar_encodings,
                    inputs_batch,
                    outputs_batch,
                    trace_val_embedding,
                    is_reversed,
                )
                times["main_forward"] = time() - start
            return result.cpu().detach().numpy(), times
        except Exception as e:
            print(e)
            raise
        finally:
            if device == "mps":
                torch.mps.empty_cache()

    def build_dataset(self, grammar, X_data, summaries, batch_size):
        return DataLoader(
            GuidingDataset(X_data, summaries),
            batch_size=batch_size,
            collate_fn=Combiner(grammar, self),
        )

    def loss_fn(
        self,
        pred,
        summaries: tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor],
    ):
        uses, mask, N, constant = summaries

        numenator = torch.sum(pred * uses, dim=1) + constant

        z = mask + pred.reshape(*pred.shape, 1)
        z = torch.logsumexp(z, dim=1)

        denominator = torch.sum(N * z, dim=1)

        result = torch.mean(denominator - numenator), torch.mean(z**2 / 1000)
        return result

    def run_training(self, train_set, lock=Lock()):
        learning_rate = 1e-3
        iterations = 5000

        train_set_size = sum(len(group) for group in train_set)
        epochs = min(math.ceil(iterations / train_set_size), 100)

        optimizer = torch.optim.Adam(
            self.parameters(), lr=learning_rate, weight_decay=1e-5
        )

        if not os.path.exists("model_checkpoints"):
            os.mkdir("model_checkpoints")

        print(f"Running training for {epochs} epochs")
        # torch.set_printoptions(profile="full")
        self.train()
        for t in range(epochs):
            losses = []
            mean_losses = []
            aux_losses = []
            with tqdm(total=train_set_size) as pbar:
                for i, data_group in enumerate(train_set):
                    for j, (grammar_encodings, (inputs, summaries)) in enumerate(
                        data_group
                    ):
                        with lock:
                            # Compute prediction and loss
                            pred = self(*grammar_encodings, *inputs)
                            mean_loss, aux_loss = self.loss_fn(pred, summaries)
                            loss = mean_loss + aux_loss
                            if torch.isnan(loss):
                                print(f"NaN loss {mean_loss.item()} {aux_loss.item()}")
                                print(i, j)
                                print(pred)
                                print(summaries)
                                raise Exception("NaN loss")

                            if loss.item() > 1e6:
                                print(
                                    f"Large loss {mean_loss.item()} {aux_loss.item()}"
                                )
                                print(i, j)
                                print(pred)
                                print(summaries)
                                raise Exception("Large loss")

                            # Backpropagation
                            loss.backward()
                            optimizer.step()
                            optimizer.zero_grad()
                            losses.append(loss.item())
                            mean_losses.append(mean_loss.item())
                            aux_losses.append(aux_loss.item())

                        pbar.update()
                        pbar.set_description(f"loss: {loss.item():>7f}")
                        wandb.log(
                            {
                                "loss": loss.item(),
                                "mean_loss": mean_loss.item(),
                                "aux_loss": aux_loss.item(),
                            }
                        )

            print(
                f"Epoch {t} finished, average loss: {np.mean(losses):>7f} {np.mean(mean_losses):>7f} {np.mean(aux_losses):>7f}, max: {max(losses):>7f} {max(mean_losses):>7f} {max(aux_losses):>7f}"
            )
            if t % 10 == 0:
                self.save(
                    os.path.join(
                        "model_checkpoints", f"{datetime.now().isoformat()}.pt"
                    )
                )
        if device == "mps":
            torch.mps.empty_cache()

    def save(self, path):
        torch.save(self.state_dict(), path)

    def load(self, path):
        self.load_state_dict(torch.load(path, weights_only=True))


def create_model():
    return GuidingModel().to(device)
