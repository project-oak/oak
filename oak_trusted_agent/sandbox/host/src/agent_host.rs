//
// Copyright 2026 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use std::sync::Arc;

use anyhow::anyhow;
use wasmtime::{
    Config, Engine, Store,
    component::{Component, Linker},
};
pub use wasmtime_wasi::p2::pipe::MemoryOutputPipe;
use wasmtime_wasi::{ResourceTable, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

wasmtime::component::bindgen!({
    path: "../wit/agent.wit",
    world: "oak-agent",
});

pub use exports::oak::agent::agent::Guest as AgentGuest;
pub use oak::agent::{
    model::{Host as ModelHost, ModelInfo, ModelProvider},
    tools::{Host as ToolsHost, ToolDescription},
};

use crate::{model_backend::ModelBackend, tool_backend::ToolBackend};

/// Configuration parameters for initializing the host state.
#[derive(Clone)]
pub struct HostConfig {
    pub model_info: ModelInfo,
    /// Backend that executes the guest's model requests.
    pub model_backend: Arc<dyn ModelBackend>,
    /// Backend that lists and executes the tools exposed to the guest.
    pub tool_backend: Arc<dyn ToolBackend>,
}

/// Host state providing implementations for host-imported WIT interfaces.
pub struct HostState {
    pub model_info: ModelInfo,
    model_backend: Arc<dyn ModelBackend>,
    tool_backend: Arc<dyn ToolBackend>,
    wasi_ctx: WasiCtx,
    table: ResourceTable,
}

impl HostState {
    /// Creates a new `HostState` from the provided `HostConfig`, inheriting
    /// host stdout and stderr.
    pub fn new(config: HostConfig) -> Self {
        let wasi_ctx = WasiCtxBuilder::new().inherit_stdout().inherit_stderr().build();
        Self::with_wasi_ctx(config, wasi_ctx)
    }

    /// Creates a new `HostState` capturing guest WASI stdout and stderr into
    /// the provided in-memory pipes.
    ///
    /// Intended for testing and verifying guest stdio / logging behavior.
    pub fn new_with_pipes(
        config: HostConfig,
        stdout: MemoryOutputPipe,
        stderr: MemoryOutputPipe,
    ) -> Self {
        let wasi_ctx = WasiCtxBuilder::new().stdout(stdout).stderr(stderr).build();
        Self::with_wasi_ctx(config, wasi_ctx)
    }

    fn with_wasi_ctx(config: HostConfig, wasi_ctx: WasiCtx) -> Self {
        Self {
            model_info: config.model_info,
            model_backend: config.model_backend,
            tool_backend: config.tool_backend,
            wasi_ctx,
            table: ResourceTable::new(),
        }
    }
}

impl WasiView for HostState {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView { ctx: &mut self.wasi_ctx, table: &mut self.table }
    }
}

impl oak::agent::tools::Host for HostState {
    fn list_tools(&mut self) -> Vec<ToolDescription> {
        self.tool_backend.list_tools()
    }

    fn call_tool(&mut self, name: String, arguments: String) -> Result<String, String> {
        self.tool_backend.call_tool(&name, &arguments).map_err(|e| format!("{e:#}"))
    }
}

impl oak::agent::model::Host for HostState {
    fn get_model_info(&mut self) -> ModelInfo {
        self.model_info.clone()
    }

    fn call_model(&mut self, request: String) -> Result<String, String> {
        self.model_backend.generate_content(&request).map_err(|e| format!("{e:#}"))
    }
}

/// Host-side sandbox environment managing Wasmtime execution of the agent
/// component.
#[derive(Clone)]
pub struct AgentSandbox {
    engine: Engine,
    linker: Linker<HostState>,
    component: Component,
}

impl AgentSandbox {
    /// Creates a new sandbox instance by loading and compiling the Wasm
    /// component bytes.
    pub fn new(component_bytes: &[u8]) -> anyhow::Result<Self> {
        let mut config = Config::new();
        config.wasm_component_model(true);

        let engine =
            Engine::new(&config).map_err(|e| anyhow!("failed to create wasmtime engine: {e}"))?;
        let mut linker = Linker::new(&engine);

        // Links the attested oak:agent interfaces defined in wit/agent.wit.
        OakAgent::add_to_linker::<_, wasmtime::component::HasSelf<_>>(
            &mut linker,
            |state: &mut HostState| state,
        )
        .map_err(|e| anyhow!("failed to link OakAgent imports: {e}"))?;

        // Links WASI Preview 2 CLI/IO interfaces.
        // Note: The attested `wit/agent.wit` interface intentionally does not declare
        // any WASI dependencies (maintaining a minimal, least-privilege interface for
        // attestation). Secure components (`adk_agent_ts`) disable WASI stdio
        // and never import these interfaces. For debug/insecure components
        // (`adk_agent_ts_insecure`), `componentize-js` automatically
        // splices WASI stdio imports into the component; linking `wasmtime_wasi` here
        // dynamically fulfills those imports without requiring WASI to be
        // exposed in `agent.wit`.
        wasmtime_wasi::p2::add_to_linker_sync(&mut linker)
            .map_err(|e| anyhow!("failed to link WASI imports: {e}"))?;

        let component = Component::from_binary(&engine, component_bytes)
            .map_err(|e| anyhow!("failed to compile agent component: {e}"))?;

        Ok(Self { engine, linker, component })
    }

    /// Creates a stateful session with a newly instantiated agent component
    /// instance.
    ///
    /// Each session receives its own isolated `Store` and WebAssembly component
    /// instance, ensuring that concurrent sessions or sessions from
    /// different users maintain strict memory isolation and are not routed
    /// to the same Wasm instance.
    pub fn create_session(&self, state: HostState) -> anyhow::Result<AgentSession> {
        let mut store = Store::new(&self.engine, state);
        let agent = OakAgent::instantiate(&mut store, &self.component, &self.linker)
            .map_err(|e| anyhow!("failed to instantiate agent component: {e}"))?;

        Ok(AgentSession { store, agent })
    }
}

/// A long-running stateful session with an instantiated agent component.
pub struct AgentSession {
    store: Store<HostState>,
    agent: OakAgent,
}

impl AgentSession {
    /// Passes a user message to the running agent instance and returns the
    /// agent's response.
    ///
    /// Note: While the Wasm instance is kept alive across `step` calls,
    /// full multi-turn conversation memory within the agent guest is being
    /// refined in a follow-up change.
    pub fn step(&mut self, user_message: &str) -> anyhow::Result<String> {
        let result = self
            .agent
            .oak_agent_agent()
            .call_run(&mut self.store, user_message)
            .map_err(|e| anyhow!("failed to call agent run: {e}"))?;

        result.map_err(|err| anyhow!("agent execution error: {err}"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct EchoModel;

    impl ModelBackend for EchoModel {
        fn generate_content(&self, request: &str) -> anyhow::Result<String> {
            Ok(format!("echo: {request}"))
        }
    }

    struct FakeTools;

    impl ToolBackend for FakeTools {
        fn list_tools(&self) -> Vec<ToolDescription> {
            vec![ToolDescription {
                name: "test_tool".to_string(),
                description: "A test tool".to_string(),
                input_schema: "{}".to_string(),
            }]
        }

        fn call_tool(&self, name: &str, arguments: &str) -> anyhow::Result<String> {
            anyhow::ensure!(name == "test_tool", "unknown tool {name}");
            Ok(format!("{name}({arguments})"))
        }
    }

    fn create_test_state() -> HostState {
        HostState::new(HostConfig {
            model_info: ModelInfo {
                name: "test-model".to_string(),
                provider: ModelProvider::Ollama,
            },
            model_backend: Arc::new(EchoModel),
            tool_backend: Arc::new(FakeTools),
        })
    }

    #[test]
    fn test_host_state_delegates_tools_to_backend() {
        let mut state = create_test_state();

        let tools = <HostState as oak::agent::tools::Host>::list_tools(&mut state);
        assert_eq!(tools.len(), 1);
        assert_eq!(tools[0].name, "test_tool");

        let result = <HostState as oak::agent::tools::Host>::call_tool(
            &mut state,
            "test_tool".to_string(),
            "{\"arg\": 1}".to_string(),
        );
        assert_eq!(result, Ok("test_tool({\"arg\": 1})".to_string()));

        let error = <HostState as oak::agent::tools::Host>::call_tool(
            &mut state,
            "missing".to_string(),
            "{}".to_string(),
        );
        assert_eq!(error, Err("unknown tool missing".to_string()));
    }

    #[test]
    fn test_host_state_delegates_model_to_backend() {
        let mut state = create_test_state();

        let model_info = <HostState as oak::agent::model::Host>::get_model_info(&mut state);
        assert_eq!(model_info.name, "test-model");
        assert!(matches!(model_info.provider, ModelProvider::Ollama));

        let result =
            <HostState as oak::agent::model::Host>::call_model(&mut state, "{}".to_string());
        assert_eq!(result, Ok("echo: {}".to_string()));
    }
}
