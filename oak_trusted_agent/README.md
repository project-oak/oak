# Trusted Agent Ecosystem

An AI agent that acts on a user's behalf needs the user's data and credentials,
and it passes both to services the agent developer does not operate:
[Model Context Protocol (MCP)](https://modelcontextprotocol.io/) tool servers
can log arguments or return prompt injections in their tool descriptions, model
servers see every prompt and tool reply in plaintext, and remote agents forward
context further down the chain. Trusting the agent author says nothing about any
of those hops.

`oak_trusted_agent` runs the agent, its MCP tools, and its model inside
[Confidential Space](https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview)
(on CPU TEEs and
[Confidential GPUs](https://cloud.google.com/confidential-computing/confidential-vm/docs/create-a-confidential-vm-instance-with-gpu)),
isolates untrusted code in
[WebAssembly Component Model](https://component-model.bytecodealliance.org/)
sandboxes, and connects the components over [Oak Proxy](../oak_proxy/README.md)
so every hop verifies hardware attestation and
[Binary Transparency](../docs/tr/README.md) endorsements before sending data:

1. The agent is built with the
   [Google Agent Development Kit (ADK)](https://google.github.io/adk-docs/),
   compiled to a WebAssembly Component Model module (`oak:agent` WIT), and run
   in Wasmtime inside a Confidential Space VM. Each client stream gets a fresh
   Wasm instance with no network or filesystem imports; its only imports are
   `oak:agent/model` and `oak:agent/tools`, which the host wires to attested
   backends.
2. Stateless MCP tool servers run [Oak Functions](../oak_functions/README.md)
   Wasm modules over read-only lookup tables in Confidential Space, fronted by
   `oak_proxy_server`. Tool code, lookup data, and MCP tool descriptions can be
   pinned by digest or checked against an endorsement log before a client
   connects.
3. [Ollama](https://ollama.com) serves
   [Gemma](https://deepmind.google/models/gemma/) on an NVIDIA H100 Confidential
   GPU behind `oak_proxy_server`, keeping prompts, tool outputs, and model
   weights in encrypted memory while in use. The same model layers run against
   benchmarks such as [AgentDojo](https://github.com/ethz-spylab/agentdojo)
   inside Confidential Space, where the provenance signer binds the benchmark
   report and the model manifest digest into a hardware attestation token that
   anyone can verify offline.

## Directories

- [`sandbox/`](sandbox/): `oak:agent` WIT interface, TypeScript ADK guest
  (`sandbox/guest/agent_ts/`), and Wasmtime host (`sandbox/host/`).
- [`server/`](server/): `TrustedAgentService` streaming gRPC server; one Wasm
  sandbox instance per client stream.
- [`agent/`](agent/): Confidential Space container and Terraform module that run
  the gRPC server and its inbound and outbound Oak Proxy tunnels.
- [`cli/`](cli/): Terminal client (`oak_trusted_agent_cli`) for multi-turn
  sessions with an agent.
- [`mcp/`](mcp/): Lookup data and reference-value helpers for attested MCP
  servers.
  - [`mcp/server/`](mcp/server/): Confidential Space MCP server wrapping Oak
    Functions and `oak_proxy_server`.
  - [`mcp/proxy/`](mcp/proxy/): HTTP proxy that checks `cosign` endorsements on
    MCP responses.
- [`model/`](model/): Ollama + Gemma container image and H100 Confidential Space
  Terraform deployment.
- [`eval/`](eval/): Benchmark harness (`agentdojo`, `hello_world`) that runs
  inside Confidential Space.
- [`provenance/`](provenance/): In-toto statement `signer`, `reader`, and
  `verifier` backed by Confidential Space attestation tokens.
- [`demo/`](demo/): Conference demos:
  - [`demo/model/`](demo/model/): Run and verify an attested AgentDojo
    evaluation of `gemma4:31b-it-qat`.
  - [`demo/mcp/`](demo/mcp/): Deploy three travel MCP servers on Confidential
    Space and detect a modified server during the handshake.
  - [`demo/agent/`](demo/agent/): Multi-turn medical assistant querying two
    isolated clinic MCP servers (`walk_in_clinic` and `gp_clinic`).
