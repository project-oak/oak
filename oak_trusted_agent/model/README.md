# Attested model server

Runs [Gemma] on [Ollama] inside [Confidential Space], fronted by [Oak Proxy] so
that an agent can establish an end-to-end encrypted, hardware-attested channel
to the model and verify that the weights evaluated in [`../eval`](../eval) are
the ones answering.

## Layout

```text
BUILD                    container image targets (:image_gemma4_31b_it_qat, :image_gemma4_e2b_it_qat)
extensions.bzl           Bazel module extension fetching Ollama model weights
oak_proxy_server.toml    oak_proxy_server configuration baked into the image
terraform/               Confidential Space deployment (VM, IAM, firewall)
```

## Building the container image

`BUILD` assembles a reproducible OCI image from the pinned `ollama/ollama` base
image, the `gemma4:31b-it-qat` weights layers (shared with the `eval` image),
and the `//oak_proxy/server` binary. A smaller `:image_gemma4_e2b_it_qat` target
is also available for smoke testing without a GPU.

Inside the container, Ollama binds to `127.0.0.1:11434` and is started as a
managed child process of `oak_proxy_server`, which listens on `0.0.0.0:8080` and
presents a Confidential Space attestation token during the Oak Session
handshake.

```shell
bazel build --config=release //oak_trusted_agent/model:image_gemma4_31b_it_qat
jq -r '.manifests[0].digest' bazel-bin/oak_trusted_agent/model/image_gemma4_31b_it_qat/index.json
```

## Deploying to Confidential Space

`terraform/` provisions a Confidential Space VM with an NVIDIA H100 Confidential
GPU (`a3-highgpu-1g` in `us-east5-a`) by default, a workload service account,
and a firewall rule for TCP port `8080` (the Oak Session WebSocket tunnel).

```shell
bazel run --config=release //oak_trusted_agent/model:push_gemma4_31b_it_qat
DIGEST="$(jq -r '.manifests[0].digest' bazel-bin/oak_trusted_agent/model/image_gemma4_31b_it_qat/index.json)"

cd oak_trusted_agent/model/terraform
terraform init
terraform apply \
  -var="image_digest=us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/model/gemma4-31b-it-qat@${DIGEST}"
```

To deploy on a CPU-only instance (`c3-standard-4`) for smoke testing without a
GPU:

```shell
terraform apply \
  -var="zone=us-central1-a" \
  -var="machine_type=c3-standard-4" \
  -var="accelerator_type=null"
```

[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
[Gemma]: https://deepmind.google/models/gemma/
[Oak Proxy]: ../../oak_proxy/README.md
[Ollama]: https://ollama.com
