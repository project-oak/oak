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
image/                   the container that runs in the TEE
terraform/               the deployment
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

## Building the container image

`image/Dockerfile` bakes Ollama, the `gemma4:e2b-it-qat` weights, the harness,
and the Bazel-built `signer` binary into a single Confidential Space image so
that the model weights are covered by the attested `image_digest`.

```shell
cd oak_trusted_agent/examples/model_eval
PUSH=false ./image/publish_docker.sh

docker run --rm \
  -e NO_ATTESTATION=true \
  -v /tmp/model_eval:/out \
  us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/model-eval/gemma4-e2b-it-qat:latest
```

## Deploying to Confidential Space

`terraform/` provisions a batch Confidential Space VM
(`tee-restart-policy=Never`) and a workload service account granted access to
the `oak-trusted-agent` GCS bucket (`gs://oak-trusted-agent/model-eval/`), where
the container uploads `report.jsonl`, `predicate.json`, and `signed.json`.

```shell
cd oak_trusted_agent/examples/model_eval
./image/publish_docker.sh

cd terraform
terraform init
terraform apply
```

## Verifying the results

Signed evaluation bundles are published to
`gs://oak-trusted-agent/model-eval/<model>/<benchmark>/`:

```shell
gcloud storage cp -r gs://oak-trusted-agent/model-eval/gemma4-e2b-it-qat/hello-world /tmp/eval_out
bazel run //oak_trusted_agent/eval/verifier:oak_trusted_agent_eval_verifier -- \
  --statement=/tmp/eval_out/hello-world/signed.json \
  --subject=/tmp/eval_out/hello-world/report.jsonl \
  --unchecked-subject=gemma4:e2b-it-qat \
  --expected-image-prefix=us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/model-eval/gemma4-e2b-it-qat \
  --expected-predicate-type=https://project-oak.dev/attestation/model-eval/v1
```

## Benchmarks

| Name          | Measures                                                      |
| ------------- | ------------------------------------------------------------- |
| `hello_world` | nothing; it exists to test the pipeline without a GPU         |
| `agentdojo`   | prompt-injection resistance on the [AgentDojo] `travel` suite |

[AgentDojo]: https://github.com/ethz-spylab/agentdojo
[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
[Ollama]: https://ollama.com
