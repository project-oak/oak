# Attested Gemma

This is an example that runs remotely attested instance of
[Gemma](https://deepmind.google/models/gemma/) model using the
[Ollama](https://ollama.com/) inference server on
[Confidential Space](https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview).
Ollama deployment uses the [Oak Proxy](oak_proxy/README.md) to create an
end-to-end encrypted attested channel between the agent and the Ollama server.

## Oak Proxy

Build Oak Proxy Client and Server:

```bash
nix develop
mkdir mcp/gemma/bin/
bazel build //oak_proxy/client:client
cp bazel-bin/oak_proxy/client/client mcp/gemma/bin/oak_proxy_client
bazel build //oak_proxy/server:server
cp bazel-bin/oak_proxy/server/server mcp/gemma/bin/oak_proxy_server
```

## Gemma

Build Gemma Docker image:

```bash
cd mcp/gemma
docker build --tag=attested-gemma:latest .
```

Run Gemma Docker container:

```bash
docker run --publish=8080:8080 --env=RUST_LOG=info attested-gemma:latest
```

## Running the Example

Run an Oak Proxy client locally:

```bash
RUST_LOG=info ./mcp/gemma/bin/oak_proxy_client --config=mcp/gemma/oak_proxy_client.toml
```

Agent configuration is provided in the [`mcp/README.md`](mcp/README.md).

Run the agent with Agent Development Kit:

```bash
adk run agent
```
