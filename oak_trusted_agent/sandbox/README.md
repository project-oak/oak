# Oak Trusted Agent Sandbox

This directory contains the WebAssembly sandbox for Oak Trusted Agents. It is
split into the agent that runs inside the sandbox and the host that runs it,
which communicate only through the `oak:agent` WIT interface.

## Layout

```text
wit/                     `oak:agent` WIT interface shared by guest and host
guest/                   agent guests compiled to Wasm components
  agent_ts/              TypeScript agent built on ADK
host/                    Wasmtime host that loads and runs agent components
```

- **Guest** (`guest/`): compiles TypeScript source code into a WebAssembly
  Component Model module adhering to the `oak:agent/agent` interface defined in
  `wit/agent.wit`. See [guest/README.md](guest/README.md).
- **Host** (`host/`): the `oak_trusted_agent_sandbox` Rust crate
  (`//oak_trusted_agent/sandbox/host`), which instantiates agent components with
  Wasmtime and provides their `oak:agent/model` and `oak:agent/tools` imports.
