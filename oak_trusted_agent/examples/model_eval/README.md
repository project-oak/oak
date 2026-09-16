# Attested model evaluation

Runs a benchmark against a model inside [Confidential Space] and signs the
result, so that a third party can check which model scored what, and which image
measured it, without trusting whoever reports the number.

The signed statement is produced here and consumed elsewhere: a client can
refuse to talk to a model whose published evaluation it cannot verify.

## Layout

```text
harness/                 runs a benchmark, builds the predicate, calls the signer
benchmarks/<name>/       one directory per benchmark
image/                   the container that runs in the TEE          (not yet)
terraform/               the deployment                              (not yet)
```

A benchmark is a Python package under `benchmarks/` defining a `Benchmark`
subclass:

```python
from benchmarks.benchmark import Benchmark


class MyBenchmark(Benchmark):
  version = "1"

  def run(self, model, out_dir) -> pathlib.Path:  # writes a report, returns its path
  def score(self, report) -> dict:                # {"score": float, "detail": {...}}
```

Nothing else in the tree knows what any particular benchmark is. `harness/`
knows about Ollama and about the predicate shape; the signer knows about in-toto
and Confidential Space and does not read the predicate at all. Adding a
benchmark is therefore a new directory under `benchmarks/`, never a change to
the harness and never a change to any Rust.

A benchmark reports a **score**, the harness wraps it in a **predicate**, and
the signer wraps that in a **statement**. The predicate shape is fixed by
[`predicate_schema.md`](predicate_schema.md). Benchmarks vary only in `detail`.

## Running it locally

Needs [Ollama] on the host, and no accelerator if the model is small enough.

```shell
ollama serve &
ollama pull gemma4:e2b

cd oak_trusted_agent/examples/model_eval
pip install -r requirements.txt
bazel build //oak_trusted_agent/eval/signer:oak_trusted_agent_eval_signer

python -m harness.run \
  --benchmark=hello_world \
  --model=gemma4:e2b \
  --out-dir=/tmp/model_eval \
  --signer=../../../bazel-bin/oak_trusted_agent/eval/signer/oak_trusted_agent_eval_signer \
  --no-attestation
```

This writes `report.jsonl`, `predicate.json` and `signed.json` to
`/tmp/model_eval/hello_world/`.

> [!WARNING] `--no-attestation` produces a statement with no proof in it, and
> the verifier rejects it. It is for checking the plumbing, not for producing
> anything anyone should believe. A real run happens inside Confidential Space,
> where the launcher issues a token naming the image that asked for it.

## Benchmarks

| Name          | Measures                                              |
| ------------- | ----------------------------------------------------- |
| `hello_world` | nothing; it exists to test the pipeline without a GPU |

[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
[Ollama]: https://ollama.com
