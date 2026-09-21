# Attested model server

Runs [Gemma] on [Ollama] inside [Confidential Space], fronted by [Oak Proxy] so
that an agent can establish an end-to-end encrypted, hardware-attested channel
to the model and verify that the exact weights evaluated in
[`../examples/model_eval`](../examples/model_eval) are the ones answering.

## Layout

```text
image/                   container image (Ollama + Gemma 4 + oak_proxy_server)
terraform/               Confidential Space deployment (VM, IAM, firewall)
```

## Building the container image

`image/Dockerfile` bakes Ollama, the `gemma4:e2b-it-qat` weights (verified
against the same `MODEL_SHA256SUM` used in `model_eval`), and the Bazel-built
`//oak_proxy/server` binary into a single Confidential Space image.

Inside the container, Ollama binds exclusively to `127.0.0.1:11434` and is
started as a managed child process of `oak_proxy_server`, which listens on
`0.0.0.0:8080` and presents a Confidential Space attestation token during the
Oak Session handshake.

```shell
cd oak_trusted_agent/model
PUSH=false ./image/publish_docker.sh
```

## Deploying to Confidential Space

`terraform/` provisions a Confidential Space VM, a least-privilege workload
service account, and a firewall rule opening TCP port `8080` for the Oak Session
WebSocket tunnel.

```shell
cd oak_trusted_agent/model
./image/publish_docker.sh

cd terraform
terraform init
terraform apply
```

To deploy on an NVIDIA H100 Confidential GPU (`a3-highgpu-1g`):

```shell
terraform apply \
  -var="zone=us-east5-a" \
  -var="machine_type=a3-highgpu-1g" \
  -var="accelerator_type=nvidia-h100-80gb"
```

[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
[Gemma]: https://deepmind.google/models/gemma/
[Oak Proxy]: ../../oak_proxy/README.md
[Ollama]: https://ollama.com
