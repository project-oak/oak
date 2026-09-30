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

use oak_trusted_agent_sandbox::{
    AgentSandbox, HostConfig, HostState, MemoryOutputPipe, ModelInfo, ModelProvider,
};

// Loads the test Wasm component binary built by Bazel via the `:adk_agent_ts`
// data dependency and located at the path injected via `ADK_AGENT_TS_WASM`.
fn load_test_wasm() -> Vec<u8> {
    let wasm_path = env!("ADK_AGENT_TS_WASM");
    std::fs::read(wasm_path)
        .unwrap_or_else(|e| panic!("Failed to read agent Wasm binary at {wasm_path}: {e}"))
}

// Loads the insecure test Wasm component binary built by Bazel via the
// `:adk_agent_ts_insecure` data dependency with WASI stdio enabled.
fn load_insecure_test_wasm() -> Vec<u8> {
    let wasm_path = env!("ADK_AGENT_TS_INSECURE_WASM");
    std::fs::read(wasm_path)
        .unwrap_or_else(|e| panic!("Failed to read insecure agent Wasm binary at {wasm_path}: {e}"))
}

fn create_test_config() -> HostConfig {
    HostConfig {
        model_info: ModelInfo { name: "test-model".to_string(), provider: ModelProvider::Gemini },
        tools: Vec::new(),
    }
}

fn create_test_host_state() -> HostState {
    HostState::new(create_test_config())
}

#[test]
fn test_agent_sandbox_runs_session_step() {
    let wasm_bytes = load_test_wasm();
    let sandbox = AgentSandbox::new(&wasm_bytes).expect("failed to create AgentSandbox");
    let mut session =
        sandbox.create_session(create_test_host_state()).expect("failed to create agent session");

    let result = session.step("What is the weather in San Francisco?");
    assert!(result.is_ok(), "agent step failed: {result:?}");
    let output = result.unwrap();
    assert_eq!(output, "Hello! I am an attested Oak Trusted Agent running inside a Wasm sandbox.");
}

#[test]
fn test_agent_sandbox_with_custom_host_state() {
    let wasm_bytes = load_test_wasm();
    let sandbox = AgentSandbox::new(&wasm_bytes).expect("failed to create AgentSandbox");

    let config = HostConfig {
        model_info: ModelInfo { name: "custom-model".to_string(), provider: ModelProvider::Ollama },
        tools: Vec::new(),
    };
    let state = HostState::new(config);
    let mut session = sandbox.create_session(state).expect("failed to create agent session");

    let result = session.step("Hello with custom state");
    assert!(result.is_ok(), "agent step with custom state failed: {result:?}");
    let output = result.unwrap();
    assert_eq!(output, "Hello! I am an attested Oak Trusted Agent running inside a Wasm sandbox.");
}

#[test]
fn test_agent_session_multi_turn() {
    let wasm_bytes = load_test_wasm();
    let sandbox = AgentSandbox::new(&wasm_bytes).expect("failed to create AgentSandbox");
    let mut session =
        sandbox.create_session(create_test_host_state()).expect("failed to create agent session");

    // First user turn
    let turn1 = session.step("First message");
    assert!(turn1.is_ok(), "turn 1 failed: {turn1:?}");
    assert_eq!(
        turn1.unwrap(),
        "Hello! I am an attested Oak Trusted Agent running inside a Wasm sandbox."
    );

    // Subsequent user turn on the same running agent session instance
    let turn2 = session.step("Second message in same session");
    assert!(turn2.is_ok(), "turn 2 failed: {turn2:?}");
    assert_eq!(
        turn2.unwrap(),
        "Hello! I am an attested Oak Trusted Agent running inside a Wasm sandbox."
    );
}

#[test]
fn test_agent_sandbox_reused_for_multiple_sessions() {
    let wasm_bytes = load_test_wasm();
    // Verify that compiling once into `AgentSandbox` allows creating multiple
    // isolated sessions by reference without consuming the sandbox.
    let sandbox = AgentSandbox::new(&wasm_bytes).expect("failed to create AgentSandbox");

    let mut session1 =
        sandbox.create_session(create_test_host_state()).expect("failed to create session 1");
    let mut session2 =
        sandbox.create_session(create_test_host_state()).expect("failed to create session 2");

    let res1 = session1.step("Message for session 1");
    let res2 = session2.step("Message for session 2");

    assert!(res1.is_ok(), "session 1 failed: {res1:?}");
    assert!(res2.is_ok(), "session 2 failed: {res2:?}");
    assert_eq!(
        res1.unwrap(),
        "Hello! I am an attested Oak Trusted Agent running inside a Wasm sandbox."
    );
    assert_eq!(
        res2.unwrap(),
        "Hello! I am an attested Oak Trusted Agent running inside a Wasm sandbox."
    );
}

#[test]
fn test_insecure_agent_sandbox_emits_logs_to_stdout() {
    let wasm_bytes = load_insecure_test_wasm();
    let sandbox = AgentSandbox::new(&wasm_bytes).expect("failed to create insecure AgentSandbox");

    let stdout_pipe = MemoryOutputPipe::new(10000);
    let stderr_pipe = MemoryOutputPipe::new(10000);
    let state =
        HostState::new_with_pipes(create_test_config(), stdout_pipe.clone(), stderr_pipe.clone());
    let mut session = sandbox.create_session(state).expect("failed to create agent session");

    let result = session.step("Hello from insecure debug sandbox");
    assert!(result.is_ok(), "insecure agent step failed: {result:?}");
    let output = result.unwrap();
    assert_eq!(output, "Hello! I am an attested Oak Trusted Agent running inside a Wasm sandbox.");

    // Verify that the insecure sandbox actively populated and emitted execution
    // logs to stdout.
    let stdout_bytes = stdout_pipe.contents();
    let logs = String::from_utf8_lossy(&stdout_bytes);
    assert!(!logs.is_empty(), "expected stdout logs from insecure sandbox, but found none");
    assert!(
        logs.contains("[User Prompt] \"Hello from insecure debug sandbox\""),
        "missing prompt log in stdout: {logs}"
    );
    assert!(logs.contains("=== Agent Session:"), "missing session header log in stdout: {logs}");
    assert!(logs.contains("[Final Answer]"), "missing final answer log in stdout: {logs}");
}

#[test]
fn test_secure_agent_sandbox_does_not_leak_logs() {
    let wasm_bytes = load_test_wasm();
    // Secure agent component (adk_agent_ts.wasm) disables WASI stdio.
    let sandbox = AgentSandbox::new(&wasm_bytes).expect("failed to create secure AgentSandbox");

    let stdout_pipe = MemoryOutputPipe::new(10000);
    let stderr_pipe = MemoryOutputPipe::new(10000);
    let state =
        HostState::new_with_pipes(create_test_config(), stdout_pipe.clone(), stderr_pipe.clone());
    let mut session = sandbox.create_session(state).expect("failed to create agent session");

    let result = session.step("Secret message in secure sandbox");
    assert!(result.is_ok(), "secure agent step failed: {result:?}");
    let output = result.unwrap();
    assert_eq!(output, "Hello! I am an attested Oak Trusted Agent running inside a Wasm sandbox.");

    // Verify that the secure sandbox DID NOT emit or leak any logs to stdout or
    // stderr.
    let stdout_bytes = stdout_pipe.contents();
    let stderr_bytes = stderr_pipe.contents();
    assert!(
        stdout_bytes.is_empty(),
        "secure sandbox leaked logs to stdout: {}",
        String::from_utf8_lossy(&stdout_bytes)
    );
    assert!(
        stderr_bytes.is_empty(),
        "secure sandbox leaked logs to stderr: {}",
        String::from_utf8_lossy(&stderr_bytes)
    );
}
