# Attested model server

Runs [Gemma] on [Ollama] inside [Confidential Space], fronted by [Oak Proxy] so
that a client can establish an end-to-end encrypted, hardware-attested channel
to the model and verify that the exact weights evaluated in
[`../examples/model_eval`](../examples/model_eval) are the ones answering.

## Layout

```text
image/                   container image (Ollama + Gemma 4 + oak_proxy_server)
terraform/               Confidential Space deployment (not yet)
oak_proxy_client.toml    client-side Oak Proxy configuration (not yet)
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

[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
[Gemma]: https://deepmind.google/models/gemma/
[Oak Proxy]: ../../oak_proxy/README.md
[Ollama]: https://ollama.com
