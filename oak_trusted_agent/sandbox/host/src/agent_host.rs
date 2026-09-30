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

/// Configuration parameters for initializing the host state.
#[derive(Clone, Debug)]
pub struct HostConfig {
    pub model_info: ModelInfo,
    pub tools: Vec<ToolDescription>,
}

/// Host state providing implementations for host-imported WIT interfaces.
pub struct HostState {
    pub model_info: ModelInfo,
    pub tools: Vec<ToolDescription>,
    wasi_ctx: WasiCtx,
    table: ResourceTable,
}

impl HostState {
    /// Creates a new `HostState` from the provided `HostConfig`, inheriting
    /// host stdout and stderr.
    pub fn new(config: HostConfig) -> Self {
        let wasi_ctx = WasiCtxBuilder::new().inherit_stdout().inherit_stderr().build();
        let table = ResourceTable::new();
        Self { model_info: config.model_info, tools: config.tools, wasi_ctx, table }
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
        let table = ResourceTable::new();
        Self { model_info: config.model_info, tools: config.tools, wasi_ctx, table }
    }
}

impl WasiView for HostState {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView { ctx: &mut self.wasi_ctx, table: &mut self.table }
    }
}

impl oak::agent::tools::Host for HostState {
    fn list_tools(&mut self) -> Vec<ToolDescription> {
        self.tools.clone()
    }

    fn call_tool(&mut self, name: String, arguments: String) -> Result<String, String> {
        // Stub implementation for now
        let args_val = serde_json::from_str::<serde_json::Value>(&arguments)
            .unwrap_or(serde_json::Value::String(arguments));
        let stub = serde_json::json!({
            "tool": name,
            "args": args_val,
        });
        Ok(stub.to_string())
    }
}

impl oak::agent::model::Host for HostState {
    fn get_model_info(&mut self) -> ModelInfo {
        self.model_info.clone()
    }

    fn call_model(&mut self, _request: String) -> Result<String, String> {
        // Stub implementation returning a canned model response
        let stub_response = serde_json::json!({
            "candidates": [{
                "content": {
                    "role": "model",
                    "parts": [{
                        "text": "Hello! I am an attested Oak Trusted Agent running inside a Wasm sandbox."
                    }]
                },
                "finishReason": "STOP"
            }]
        });
        Ok(stub_response.to_string())
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

    fn create_test_config() -> HostConfig {
        HostConfig {
            model_info: ModelInfo {
                name: "test-model".to_string(),
                provider: ModelProvider::Gemini,
            },
            tools: vec![ToolDescription {
                name: "test_tool".to_string(),
                description: "A test tool".to_string(),
                input_schema: "{}".to_string(),
            }],
        }
    }

    #[test]
    fn test_host_config_and_state_constructor() {
        let config = create_test_config();
        let state = HostState::new(config);
        assert_eq!(state.model_info.name, "test-model");
        assert!(matches!(state.model_info.provider, ModelProvider::Gemini));
        assert_eq!(state.tools.len(), 1);
        assert_eq!(state.tools[0].name, "test_tool");
    }

    #[test]
    fn test_host_state_tools_implementation() {
        let mut state = HostState::new(create_test_config());

        let tools = <HostState as oak::agent::tools::Host>::list_tools(&mut state);
        assert_eq!(tools.len(), 1);
        assert_eq!(tools[0].name, "test_tool");

        let call_res = <HostState as oak::agent::tools::Host>::call_tool(
            &mut state,
            "test_tool".to_string(),
            "{\"arg\": 1}".to_string(),
        );
        assert!(call_res.is_ok());
        let res_str = call_res.unwrap();
        assert!(res_str.contains("test_tool"));
        assert!(res_str.contains("arg"));
    }

    #[test]
    fn test_host_state_tools_invalid_json_handling() {
        let mut state = HostState::new(create_test_config());
        let call_res = <HostState as oak::agent::tools::Host>::call_tool(
            &mut state,
            "test_tool".to_string(),
            "plain string argument".to_string(),
        );
        assert!(call_res.is_ok());
        let res_str = call_res.unwrap();
        assert!(res_str.contains("plain string argument"));
    }

    #[test]
    fn test_host_state_model_implementation() {
        let mut state = HostState::new(create_test_config());
        let model_info = <HostState as oak::agent::model::Host>::get_model_info(&mut state);
        assert_eq!(model_info.name, "test-model");

        let model_res =
            <HostState as oak::agent::model::Host>::call_model(&mut state, "{}".to_string());
        assert!(model_res.is_ok());
        let body = model_res.unwrap();
        assert!(body.contains("candidates"));
    }
}
