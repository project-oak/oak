# Trusted Model Evaluation Demo

Demonstrates how a model provider or independent auditor evaluates
`gemma4:31b-it-qat` against the [AgentDojo] prompt-injection benchmark inside a
Google Cloud [Confidential Space] TEE on an NVIDIA H100 GPU, publishes the
signed evaluation bundle to GCS, and allows any third party to cryptographically
verify the result offline before trusting the model.

## Files

| File               | Purpose                                                                                                                                      |
| ------------------ | -------------------------------------------------------------------------------------------------------------------------------------------- |
| `terraform.tfvars` | Terraform configuration targeting an `a3-highgpu-1g` (NVIDIA H100 80 GB) Confidential Space VM in `us-east5-a` for the `agentdojo` benchmark |
| `run.sh`           | Builds & pushes the reproducible `gemma4:31b-it-qat` eval image, runs the benchmark in Confidential Space, and tears down the H100 VM        |
| `get.sh`           | Downloads a published evaluation bundle from `gs://oak-trusted-agent/eval/gemma4-31b-it-qat/` into a local directory                         |
| `verify.sh`        | Runs the provenance verifier against the downloaded evaluation bundle                                                                        |

## Step 1: Run the attested evaluation in Confidential Space (Pre-demo)

Run from the repository root inside `nix develop`:

```shell
./oak_trusted_agent/demo/model/run.sh agentdojo
```

What this does:

1. Builds the hermetic OCI container image
   `//oak_trusted_agent/eval:image_gemma4_31b_it_qat`, which bundles the pinned
   `ollama/ollama` base image, the `gemma4:31b-it-qat` weights layers (shared
   with `//oak_trusted_agent/model:image_gemma4_31b_it_qat`), the AgentDojo
   harness, and the provenance signer binary.
2. Pushes the image to Artifact Registry and reads its reproducible manifest
   digest (`sha256:…`).
3. Provisions a batch Confidential Space H100 VM (`tee-restart-policy=Never`)
   pinned to that exact image digest.
4. Inside the TEE, Ollama serves `gemma4:31b-it-qat` on `127.0.0.1:11434`, the
   harness runs the AgentDojo `travel` prompt-injection suite, and the signer
   hashes `report.jsonl`, embeds the model manifest digest and score in an
   in-toto v1 `Statement`, and binds the statement digest to a Confidential
   Space hardware attestation token (`eat_nonce`).
5. Uploads `report.jsonl`, `predicate.json`, and `signed.json` to
   `gs://oak-trusted-agent/eval/gemma4-31b-it-qat/agentdojo/`, then destroys the
   H100 VM.

To run the fast pipeline smoke test (`hello_world`) as well:

```shell
./oak_trusted_agent/demo/model/run.sh hello_world
```

## Step 2: Download & verify the published evaluation (Live / Recorded Demo)

Anyone can download the published evaluation bundle to `/tmp/trusted_eval/` and
verify it locally in a few seconds without needing a GPU or TEE:

```shell
./oak_trusted_agent/demo/model/get.sh /tmp/trusted_eval
./oak_trusted_agent/demo/model/verify.sh /tmp/trusted_eval
```

Expected output:

```text
📜 Statement
  predicate type  https://project-oak.github.io/oak/trusted_agent/eval/v1
  subject         report.jsonl (sha256:e3238df964872e37eb974e8057c4cb2ab83bb7db18707d4aefc8844b277bbbc7)
  subject         gemma4:31b-it-qat (sha256:e0812a55773bfeac846b2d605b4d93638b8dfa7119d9587f3d91475afc78185e)

📊 Predicate
  benchmark       {"name":"agentdojo","version":"v1.2.2"}
  model           {"name":"gemma4:31b-it-qat","digest":"sha256:e0812a55773bfeac846b2d605b4d93638b8dfa7119d9587f3d91475afc78185e","parameters":"30.7B","quantization":"Q4_0","sampling":{"temperature":0.0,"seed":0}}
  score           1.0
  detail          {"suite":"travel","attack":"direct","trials":4,"resisted":4,"attack_success_rate":0.0,"utility_rate":1.0}
  run             {"started_at":"2026-10-01T22:45:46Z","finished_at":"2026-10-01T22:48:08Z"}

🔍 Correctness
  ✅ the envelope declares the in-toto media type
  ✅ the payload is an in-toto v1 Statement
  ✅ the predicate type is the expected one
  ✅ every subject was re-hashed or waived

🔐 Attestation
  ✅ report.jsonl matches the digest in the statement
  ✅ a Confidential Space token binds this exact statement
  ✅ the workload image is the expected one
     ├── image      us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/eval/gemma4-31b-it-qat@sha256:8298158ab52767d7b9ce3b190b38319a8a39fe5a43d57cf420f4d51801a83fed
     ├── digest     sha256:8298158ab52767d7b9ce3b190b38319a8a39fe5a43d57cf420f4d51801a83fed
     └── issued at  2026-10-01T22:48:17.000Z

✅ VERIFIED
```

### What each section shows on screen

- **`📜 Statement` & `📊 Predicate`:** Shows the two artifacts covered by the
  in-toto statement (`report.jsonl` and the `gemma4:31b-it-qat` Ollama manifest
  digest) and the benchmark score and details recorded by the harness.
- **`🔍 Correctness`:** Confirms the envelope and in-toto v1 statement structure
  are valid and that no subject in the statement went unaccounted for. The 19 GB
  model weights are waived from local re-hashing
  (`--unchecked-subject=gemma4:31b-it-qat`) because their layers are baked into
  the reproducible workload image verified under `🔐 Attestation`.
- **`🔐 Attestation`:** Re-hashes the downloaded `report.jsonl` against the
  statement, verifies the Confidential Space hardware attestation token against
  Google's Confidential Space root certificate (`eat_nonce == SHA256(payload)`),
  and confirms the workload container image reference and exact digest.

### Step 3: Tamper-detection check

To show that modifying a single byte of the report invalidates the proof:

```shell
echo '{"tampered": true}' >> /tmp/trusted_eval/report.jsonl
./oak_trusted_agent/demo/model/verify.sh /tmp/trusted_eval
```

This fails with
`❌ report.jsonl matches the digest in the statement: the file does not match its digest`
and exits with `❌ NOT VERIFIED (1 check(s) failed)`.

[AgentDojo]: https://github.com/ethz-spylab/agentdojo
[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
