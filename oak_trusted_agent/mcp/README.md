# Trusted MCP

[Model Context Protocol (MCP)] server, endorsement proxy, and helpers:

- [`server/`](server/README.md): Attested MCP server wrapping [Oak Functions]
  for stateless key-value lookups inside [Confidential Space], fronted by [Oak
  Proxy].
- [`proxy/`](proxy/README.md): HTTP proxy that checks `cosign` endorsements on
  MCP server responses.
- `create_lookup_data.py`: Converts JSON datasets into the
  `oak.functions.LookupDataChunk` textproto format consumed by Oak Functions.
- `generate_reference_values.rs`: Generates a `ReferenceValuesCollection`
  protobuf pinning the Confidential Space root certificate and expected
  container image digest.

[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
[Model Context Protocol (MCP)]: https://modelcontextprotocol.io/
[Oak Functions]: ../../oak_functions/README.md
[Oak Proxy]: ../../oak_proxy/README.md
