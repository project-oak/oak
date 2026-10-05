# Trusted Model Evaluation Demo

Evaluates `gemma4:31b-it-qat` against the [AgentDojo] prompt-injection benchmark
inside a [Confidential Space] VM with an NVIDIA H100 GPU, publishes the signed
evaluation bundle to GCS, and verifies the bundle offline.

## Files

| File               | Purpose                                                                                                             |
| ------------------ | ------------------------------------------------------------------------------------------------------------------- |
| `terraform.tfvars` | Terraform variables targeting an `a3-highgpu-1g` (NVIDIA H100 80 GB) VM in `us-east5-a` for `agentdojo`             |
| `run.sh`           | Builds and pushes the `gemma4:31b-it-qat` eval image, runs the benchmark in Confidential Space, and destroys the VM |
| `get.sh`           | Downloads a published evaluation bundle from `gs://oak-trusted-agent/eval/gemma4-31b-it-qat/`                       |
| `read.sh`          | Prints the in-toto `Statement` and `Predicate` from `signed.json`                                                   |
| `verify.sh`        | Runs the provenance verifier against the downloaded bundle                                                          |

## 1. Run the evaluation in Confidential Space

From the repository root inside `nix develop`:

```shell
./oak_trusted_agent/demo/model/run.sh agentdojo
```

`run.sh` builds and pushes `//oak_trusted_agent/eval:image_gemma4_31b_it_qat`,
which bundles `ollama/ollama`, the `gemma4:31b-it-qat` weights layers (shared
with `//oak_trusted_agent/model:image_gemma4_31b_it_qat`), the AgentDojo
harness, and the provenance signer. It then boots a batch Confidential Space
H100 VM (`tee-restart-policy=Never`) pinned to that image digest. Inside the VM,
Ollama serves `gemma4:31b-it-qat` on `127.0.0.1:11434`, the harness runs the
AgentDojo `travel` suite, and the signer binds `report.jsonl`, the model
manifest digest, and the predicate into a Confidential Space attestation token
(`eat_nonce`). When the container uploads `report.jsonl`, `predicate.json`, and
`signed.json` to `gs://oak-trusted-agent/eval/gemma4-31b-it-qat/agentdojo/`, the
script tears the VM down.

To run the fast pipeline smoke test (`hello_world`):

```shell
./oak_trusted_agent/demo/model/run.sh hello_world
```

## 2. Download, read, and verify the published bundle

Download the bundle to `/tmp/trusted_eval/` and inspect its statement and
predicate:

```shell
./oak_trusted_agent/demo/model/get.sh /tmp/trusted_eval
./oak_trusted_agent/demo/model/read.sh /tmp/trusted_eval
```

```text
── 📜 Statement ────────────────────────────────────────────────────────────────
  predicate type   https://project-oak.github.io/oak/trusted_agent/eval/v1
  subject          report.jsonl       sha256:debef058151c1e65638dfdcea51e73cf107eeb9d5589c62781aee1ae892c1235
  subject          gemma4:31b-it-qat  sha256:e0812a55773bfeac846b2d605b4d93638b8dfa7119d9587f3d91475afc78185e

── 📊 Predicate ────────────────────────────────────────────────────────────────
  benchmark        agentdojo v1.2.2
  model            gemma4:31b-it-qat (30.7B, Q4_0, temperature=0, seed=0)
  run              2026-10-02T09:17:54Z → 2026-10-02T10:38:51Z
  detail
     ├── attack_success_rate   0.0071
     └── utility_rate          0.85
```

Verify the bundle:

```shell
./oak_trusted_agent/demo/model/verify.sh /tmp/trusted_eval
```

```text
── 🔐 Attestation ──────────────────────────────────────────────────────────────
  ✅ Subject report.jsonl matches the digest in the statement
  ✅ A Confidential Space token binds this exact statement
  ✅ The workload image is the expected one
     ├── image      us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/eval/gemma4-31b-it-qat
     ├── digest     sha256:0b0d5ef834a6c06bd59697ebdb1c16421fb8ff8fc3541cb714f93d7cfd747528
     └── issued at  2026-10-02T10:39:01.000Z

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
✅ VERIFIED
```

The verifier re-hashes `/tmp/trusted_eval/report.jsonl` against the statement,
checks the Confidential Space token against Google's Confidential Space root
certificate (`eat_nonce == SHA256(payload)`), and checks the container image
reference and digest. The 19 GB model weights are waived from local re-hashing
(`--unchecked-subject=gemma4:31b-it-qat`) because their layers are baked into
the verified workload image.

## 3. Tamper check

Flipping the failed trial in `report.jsonl` breaks the subject digest check:

```shell
sed -i 's/"resisted": false/"resisted": true/' /tmp/trusted_eval/report.jsonl
./oak_trusted_agent/demo/model/verify.sh /tmp/trusted_eval
```

```text
  ❌ Subject report.jsonl matches the digest in the statement
     └── the file does not match its digest
```

[AgentDojo]: https://github.com/ethz-spylab/agentdojo
[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
