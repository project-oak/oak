# Oak Trusted Agent Sandbox

WebAssembly sandbox for Oak Trusted Agents, split into the agent that runs
inside the sandbox and the host that runs it. The two communicate only through
the `oak:agent` WIT interface.

## Layout

```text
wit/                     `oak:agent` WIT interface shared by guest and host
guest/                   agent guests compiled to Wasm components
  agent_ts/              TypeScript agent built on ADK
host/                    Wasmtime host that loads and runs agent components
```

- [`guest/`](guest/README.md): compiles agent source code into a WebAssembly
  Component Model module implementing `oak:agent/agent` (`wit/agent.wit`).
- `host/`: the `oak_trusted_agent_sandbox` Rust crate
  (`//oak_trusted_agent/sandbox/host`), which instantiates agent components with
  Wasmtime and supplies their `oak:agent/model` and `oak:agent/tools` imports.
