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

//! Runs the CLI binary against an in-process `TrustedAgentService` serving the
//! real agent Wasm component with a fake model.

use std::{
    io::Write,
    process::{Command, Output, Stdio},
    sync::Arc,
};

use oak_grpc::oak::trusted_agent::v1::trusted_agent_service_server::TrustedAgentServiceServer;
use oak_trusted_agent_sandbox::{
    AgentSandbox, HostConfig, ModelBackend, ModelInfo, ModelProvider, NoTools,
};
use oak_trusted_agent_server::TrustedAgentServiceImpl;
use tokio_stream::wrappers::TcpListenerStream;
use tonic::transport::Server;

/// Model backend that echoes the latest user message.
struct EchoModel;

impl ModelBackend for EchoModel {
    fn generate_content(&self, request: &str) -> anyhow::Result<String> {
        let request: serde_json::Value = serde_json::from_str(request)?;
        let user_text = request["contents"]
            .as_array()
            .and_then(|contents| contents.iter().rev().find(|c| c["role"] == "user"))
            .and_then(|content| content["parts"][0]["text"].as_str())
            .unwrap_or_default()
            .to_string();
        Ok(serde_json::json!({
            "candidates": [{
                "content": {"role": "model", "parts": [{"text": format!("echo: {user_text}")}]},
                "finishReason": "STOP",
            }],
        })
        .to_string())
    }
}

/// Serves `TrustedAgentService` on a local port and returns its URL.
async fn start_service() -> String {
    let wasm_path = env!("ADK_AGENT_TS_WASM");
    let wasm_bytes = std::fs::read(wasm_path)
        .unwrap_or_else(|e| panic!("failed to read agent Wasm binary at {wasm_path}: {e}"));
    let sandbox = AgentSandbox::new(&wasm_bytes).expect("failed to create AgentSandbox");
    let host_config = HostConfig {
        model_info: ModelInfo { name: "test-model".to_string(), provider: ModelProvider::Ollama },
        model_backend: Arc::new(EchoModel),
        tool_backend: Arc::new(NoTools),
    };
    let server = TrustedAgentServiceServer::new(TrustedAgentServiceImpl::new(sandbox, host_config));

    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let address = listener.local_addr().unwrap();
    tokio::spawn(async move {
        Server::builder()
            .add_service(server)
            .serve_with_incoming(TcpListenerStream::new(listener))
            .await
            .unwrap();
    });
    format!("http://{address}")
}

/// Runs `open --agent-url <agent_url>` with `input` on stdin, without blocking
/// the async runtime.
async fn open(agent_url: &str, input: &str) -> Output {
    let agent_url = agent_url.to_string();
    let input = input.to_string();
    tokio::task::spawn_blocking(move || {
        let mut child = Command::new(env!("OAK_TRUSTED_AGENT_CLI"))
            .args(["open", "--agent-url", &agent_url])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("failed to run the CLI");
        // Dropping stdin after writing ends the input.
        child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
        child.wait_with_output().expect("failed to wait for the CLI")
    })
    .await
    .unwrap()
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[tokio::test(flavor = "multi_thread")]
async fn test_open_send_close() {
    let agent_url = start_service().await;

    // Each line is a new turn on the same stream; empty lines are skipped, and
    // nothing after `close` is sent.
    let output = open(&agent_url, "Hello agent\n\nHello again\nclose\nIgnored\n").await;

    assert!(output.status.success(), "open failed: {}", stderr(&output));
    let stdout = stdout(&output);
    assert!(stdout.contains("✅ Opened a stream"), "{stdout}");
    assert!(stdout.contains("agent> echo: Hello agent\n"), "{stdout}");
    assert!(stdout.contains("agent> echo: Hello again\n"), "{stdout}");
    assert!(!stdout.contains("Ignored"), "{stdout}");
    assert!(stdout.contains("✅ Closed the stream."), "{stdout}");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_end_of_input_closes_stream() {
    let agent_url = start_service().await;

    let output = open(&agent_url, "Hello\n").await;

    assert!(output.status.success(), "open failed: {}", stderr(&output));
    let stdout = stdout(&output);
    assert!(stdout.contains("agent> echo: Hello\n"), "{stdout}");
    assert!(stdout.contains("✅ Closed the stream."), "{stdout}");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_concurrent_opens_are_independent() {
    let agent_url = start_service().await;

    let (first, second) =
        tokio::join!(open(&agent_url, "first\nclose\n"), open(&agent_url, "second\nclose\n"));

    for (output, text) in [(&first, "first"), (&second, "second")] {
        assert!(output.status.success(), "open failed: {}", stderr(output));
        assert!(stdout(output).contains(&format!("agent> echo: {text}\n")), "{}", stdout(output));
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_open_fails_without_agent() {
    // Nothing listens on the port once the listener is dropped.
    let port = std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();

    let output = open(&format!("http://127.0.0.1:{port}"), "Hello\n").await;

    assert!(!output.status.success(), "open must fail without an agent");
    assert!(stderr(&output).contains("failed to open a stream"), "{}", stderr(&output));
    assert!(stderr(&output).contains("failed to connect to the agent"), "{}", stderr(&output));
    // Only failures after connecting may be caused by attestation.
    assert!(!stderr(&output).contains("attestation"), "{}", stderr(&output));
    assert!(!stdout(&output).contains("agent>"), "{}", stdout(&output));
}
