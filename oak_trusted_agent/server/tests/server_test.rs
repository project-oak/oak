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

use oak_grpc::oak::trusted_agent::v1::{
    trusted_agent_service_client::TrustedAgentServiceClient,
    trusted_agent_service_server::TrustedAgentServiceServer,
};
use oak_proto_rust::oak::trusted_agent::v1::{
    AgentRequest, UserMessage, agent_request::Request as ProtoRequest,
    agent_response::Response as ProtoResponse,
};
use oak_trusted_agent_sandbox::{
    AgentSandbox, HostConfig, ModelBackend, ModelInfo, ModelProvider, NoTools,
};
use oak_trusted_agent_server::TrustedAgentServiceImpl;
use tokio_stream::wrappers::{ReceiverStream, TcpListenerStream};
use tonic::transport::{Channel, Server};

/// Model backend that always answers with the same text.
struct CannedModel;

impl ModelBackend for CannedModel {
    fn generate_content(&self, _request: &str) -> anyhow::Result<String> {
        Ok(serde_json::json!({
            "candidates": [{
                "content": {"role": "model", "parts": [{"text": "Hello from the canned model."}]},
                "finishReason": "STOP",
            }],
        })
        .to_string())
    }
}

fn load_test_wasm() -> Vec<u8> {
    let wasm_path = env!("ADK_AGENT_TS_WASM");
    std::fs::read(wasm_path)
        .unwrap_or_else(|e| panic!("Failed to read agent Wasm binary at {wasm_path}: {e}"))
}

/// Serves `TrustedAgentService` on a local port and returns a connected client.
async fn start_service() -> TrustedAgentServiceClient<Channel> {
    let wasm_bytes = load_test_wasm();
    let sandbox = AgentSandbox::new(&wasm_bytes).expect("failed to create AgentSandbox");

    let host_config = HostConfig {
        model_info: ModelInfo { name: "test-model".to_string(), provider: ModelProvider::Gemini },
        model_backend: Arc::new(CannedModel),
        tool_backend: Arc::new(NoTools),
    };
    let service = TrustedAgentServiceImpl::new(sandbox, host_config);
    let server = TrustedAgentServiceServer::new(service);

    let listener = tokio::net::TcpListener::bind("[::]:0").await.unwrap();
    let local_addr = listener.local_addr().unwrap();
    let stream = TcpListenerStream::new(listener);

    tokio::spawn(async move {
        Server::builder().add_service(server).serve_with_incoming(stream).await.unwrap();
    });

    let channel =
        tonic::transport::Channel::from_shared(format!("http://[::1]:{}", local_addr.port()))
            .unwrap()
            .connect()
            .await
            .unwrap();

    TrustedAgentServiceClient::new(channel)
}

#[tokio::test]
async fn test_streaming_service_session_lifecycle() {
    let mut client = start_service().await;

    // Open first streaming session
    let (tx1, rx1) = tokio::sync::mpsc::channel(10);
    let request_stream1 = ReceiverStream::new(rx1);
    let response1 = client.stream(request_stream1).await.unwrap();
    let mut response_stream1 = response1.into_inner();

    // Send first message in session 1
    tx1.send(AgentRequest {
        request: Some(ProtoRequest::UserMessage(UserMessage {
            text: "Hello from session 1 - turn 1".to_string(),
        })),
    })
    .await
    .unwrap();

    let resp = response_stream1.message().await.unwrap().expect("expected response");
    match resp.response {
        Some(ProtoResponse::AgentMessage(msg)) => {
            assert!(!msg.text.is_empty(), "agent message was empty");
        }
        other => panic!("expected AgentMessage, got {other:?}"),
    }

    // Send second message in session 1 (multi-turn conversation within the same
    // session)
    tx1.send(AgentRequest {
        request: Some(ProtoRequest::UserMessage(UserMessage {
            text: "Hello from session 1 - turn 2".to_string(),
        })),
    })
    .await
    .unwrap();

    let resp = response_stream1.message().await.unwrap().expect("expected response");
    match resp.response {
        Some(ProtoResponse::AgentMessage(msg)) => {
            assert!(!msg.text.is_empty(), "agent message was empty");
        }
        other => panic!("expected AgentMessage, got {other:?}"),
    }

    // Drop client transmitter to close session 1
    drop(tx1);

    // Verify stream terminates on client side
    let end_resp = response_stream1.message().await.unwrap();
    assert!(end_resp.is_none(), "stream should terminate cleanly after transmitter is dropped");

    // Open second independent streaming session to verify sandbox creates a new
    // session cleanly
    let (tx2, rx2) = tokio::sync::mpsc::channel(10);
    let request_stream2 = ReceiverStream::new(rx2);
    let response2 = client.stream(request_stream2).await.unwrap();
    let mut response_stream2 = response2.into_inner();

    tx2.send(AgentRequest {
        request: Some(ProtoRequest::UserMessage(UserMessage {
            text: "Hello from session 2".to_string(),
        })),
    })
    .await
    .unwrap();

    let resp = response_stream2.message().await.unwrap().expect("expected response");
    match resp.response {
        Some(ProtoResponse::AgentMessage(msg)) => {
            assert!(!msg.text.is_empty(), "agent message was empty");
        }
        other => panic!("expected AgentMessage, got {other:?}"),
    }

    drop(tx2);
    let end_resp2 = response_stream2.message().await.unwrap();
    assert!(end_resp2.is_none());
}

#[tokio::test]
async fn test_invalid_request_ends_stream_with_error() {
    let mut client = start_service().await;

    let (tx, rx) = tokio::sync::mpsc::channel(10);
    let mut response_stream = client.stream(ReceiverStream::new(rx)).await.unwrap().into_inner();

    // A request without a message cannot be processed, so the server ends the
    // stream with an error status instead of sending a response.
    tx.send(AgentRequest { request: None }).await.unwrap();

    let status = response_stream.message().await.expect_err("expected an error status");
    assert_eq!(status.code(), tonic::Code::InvalidArgument);
    assert!(response_stream.message().await.unwrap().is_none(), "stream should have ended");
}
