# Attested Oak Functions MCP server

Exposes an [Oak Functions] Wasm module and read-only lookup table over the
[Model Context Protocol (MCP)] inside [Confidential Space], fronted by [Oak
Proxy] for end-to-end encrypted, hardware-attested sessions.

The server container is generic: the Wasm module (`WASM_URL`), lookup data
(`LOOKUP_DATA_URL`), and MCP tool definition (`TOOL_CONFIG_URL`) are provided
via Confidential Space launch environment variables at deployment time.

## Building and pushing the container image

```shell
bazel build --config=release //oak_trusted_agent/mcp/server:oak_functions_mcp_server_image
bazel run --config=release //oak_trusted_agent/mcp/server:oak_functions_mcp_server_push
```

## Deploying to Confidential Space

```shell
cd oak_trusted_agent/mcp/server/terraform
terraform init
terraform apply -var-file=/path/to/service.tfvars
```

[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
[Model Context Protocol (MCP)]: https://modelcontextprotocol.io/
[Oak Functions]: ../../../oak_functions/README.md
[Oak Proxy]: ../../../oak_proxy/README.md
