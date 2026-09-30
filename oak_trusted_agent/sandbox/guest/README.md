# Oak Trusted Agent Sandbox Guests

Agents that run inside the Oak Trusted Agent sandbox. Each guest is compiled to
a WebAssembly component that implements the `oak:agent` world defined in
[`../wit/agent.wit`](../wit/agent.wit), and lives in its own Bazel package with
its own toolchain and dependency lockfile.

- [`agent_ts/`](agent_ts/README.md): TypeScript agent built on ADK
  (`//oak_trusted_agent/sandbox/guest/agent_ts:adk_agent_ts`).
