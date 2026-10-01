# Attested agent host

Runs the [Oak Trusted Agent] host inside [Confidential Space], fronted by an
inbound [Oak Proxy] server and connected to an attested [Model server] and an
arbitrary number of attested MCP tool servers via outbound [Oak Proxy] client
tunnels.

## Layout

```text
config/                  inbound and outbound Oak Proxy TOML configurations
src/                     agent entrypoint and proxy mesh orchestration
terraform/               reusable Confidential Space deployment module
```

## Architecture

At startup, `/bin/oak_trusted_agent` orchestrates the container's proxy mesh:

1. **Inbound (`oak_proxy_server`)**: Listens on `0.0.0.0:8080`, presents the
   agent VM's Confidential Space attestation evidence during the Oak Session
   handshake, and forwards decrypted requests to `127.0.0.1:8081`.
2. **Outbound Model (`oak_proxy_client`)**: Listens on `127.0.0.1:11434` and
   tunnels model inference requests over an attested Oak Session to
   `MODEL_PROXY_URL`, verifying the peer's Confidential Space attestation
   against `/etc/confidential_space_root.pem`.
3. **Outbound MCP tools (`oak_proxy_client` $\times N$)**: For each
   comma-separated WebSocket URL in `MCP_PROXY_URLS`, launches a dedicated
   `oak_proxy_client` listening on `127.0.0.1:$((8090 + i))`, exposing local
   Streamable HTTP MCP endpoints (`http://127.0.0.1:8090/mcp`,
   `http://127.0.0.1:8091/mcp`, ...) to the sandboxed agent.

Before starting the proxy mesh, it fetches the agent Wasm component and the
model configuration over HTTP(S) (e.g. from a GCS bucket), loads the component
into the [Oak Trusted Agent] sandbox and then serves the `TrustedAgentService`
streaming gRPC interface ([trusted_agent.proto]) on `AGENT_LISTEN_ADDRESS`. Each
client stream gets its own isolated Wasm instance.

The gRPC interface is plaintext and unattested, so the agent refuses to listen
on anything other than a loopback address. The only ingress path is the Oak
Session terminated by the inbound `oak_proxy_server`:

```text
gRPC client -> oak_proxy_client -> (Oak Session over WebSocket)
            -> oak_proxy_server -> agent (127.0.0.1:8081) -> Wasm sandbox
```

The sandbox's model calls go to the Ollama chat API (`/api/chat`) served by the
outbound Model `oak_proxy_client`, and its tool calls go to the MCP servers
served by the outbound MCP `oak_proxy_client`s. The host translates the guest's
GenerateContent-style requests to the Ollama API, and exposes the tools of all
MCP servers to the guest. Tool names must be unique across MCP servers.

The sandbox is configured with the following flags (or environment variables),
which have no defaults. The container image allows the operator to override them
via the Confidential Space launch policy.

- `--wasm-url` (`WASM_URL`): URL of the agent Wasm component, e.g. a GCS object
  built from `//oak_trusted_agent/sandbox/guest/agent_ts:adk_agent_ts`.
- `--model-config-url` (`MODEL_CONFIG_URL`): URL of the JSON model configuration
  exposed to the agent. Unknown fields are rejected and `provider` must be
  `ollama`. `gemini` is part of the guest interface but has no backend yet, so
  the agent refuses to start with it:

  ```json
  { "name": "gemma4:31b-it-qat", "provider": "ollama" }
  ```

## Testing

Unit tests cover the proxy mesh planning and the model config parsing.

```shell
nix develop --command bazel test //oak_trusted_agent/agent:all
```

## Building and pushing the container image

```shell
# Build the OCI image
nix develop --command bazel build //oak_trusted_agent/agent:image

# Push the image to Artifact Registry
nix develop --command bazel run //oak_trusted_agent/agent:push
```

## Deploying to Confidential Space

`terraform/` can be used standalone or instantiated as a reusable Terraform
module by composite deployments (such as `oak_trusted_agent/demo/agent/`):

```hcl
module "trusted_agent" {
  source = "../../agent/terraform"

  gcp_project_id    = var.gcp_project_id
  zone              = var.zone
  instance_name     = "medical-trusted-agent"
  image_digest      = var.agent_image_digest
  wasm_url          = "https://storage.googleapis.com/oak-trusted-agent/demo/agent/adk_agent_ts.wasm"
  model_config_url  = "https://storage.googleapis.com/oak-trusted-agent/demo/agent/model_config.json"
  model_server_ip   = module.trusted_model.internal_ip
  mcp_server_ips    = [
    module.walk_in_clinic_mcp.internal_ip,
    module.gp_clinic_mcp.internal_ip,
  ]
  system_prompt_url = "https://storage.googleapis.com/oak-trusted-agent/demo/agent/prompts/system.md"
}
```

[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
[Model server]: ../model/README.md
[Oak Proxy]: ../../oak_proxy/README.md
[Oak Trusted Agent]: ../sandbox/README.md
[trusted_agent.proto]: ../../proto/oak_trusted_agent/service/trusted_agent.proto
