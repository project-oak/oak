# Trusted MCP

Reusable [Model Context Protocol (MCP)] building blocks for the Trusted Agent
Ecosystem:

- [`server/`](server/README.md): Attested MCP server wrapping [Oak Functions]
  for stateless, privacy-preserving key-value lookups inside [Confidential
  Space], fronted by [Oak Proxy].
- `create_lookup_data.py`: Converts structured JSON datasets into the
  `oak.functions.LookupDataChunk` textproto format consumed by Oak Functions.
- `generate_reference_values.rs`: Generates a `ReferenceValuesCollection`
  protobuf pinning the Confidential Space root certificate and expected
  container image digest.

[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
[Model Context Protocol (MCP)]: https://modelcontextprotocol.io/
[Oak Functions]: ../../oak_functions/README.md
[Oak Proxy]: ../../oak_proxy/README.md
