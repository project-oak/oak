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

use oak_grpc::oak::trusted_agent::v1::trusted_agent_service_server::TrustedAgentService;
use oak_proto_rust::oak::trusted_agent::v1::{
    AgentMessage, AgentRequest, AgentResponse, agent_request::Request as ProtoRequest,
    agent_response::Response as ProtoResponse,
};
use oak_trusted_agent_sandbox::{AgentSandbox, HostConfig, HostState};
use tokio_stream::{StreamExt, wrappers::ReceiverStream};
use tonic::{Request, Response, Status, Streaming};

/// Number of responses that can be queued for a client before the session
/// waits for the client to read them. The session produces one response per
/// request, so this only bounds how far a slow reader can fall behind.
const RESPONSE_BUFFER_SIZE: usize = 32;

/// Implementation of the `TrustedAgentService` gRPC service.
///
/// Every `Stream` RPC spins up a new, dedicated Wasm sandbox instance. That
/// instance stays alive for the whole lifetime of the stream, so all of the
/// stream's turns share its state, and it is torn down when the stream ends.
/// Instances are never shared or reused across streams.
///
/// User messages on a stream are processed sequentially. If the agent fails to
/// process a message, the stream is terminated with an error status.
pub struct TrustedAgentServiceImpl {
    sandbox: AgentSandbox,
    host_config: HostConfig,
}

impl TrustedAgentServiceImpl {
    pub fn new(sandbox: AgentSandbox, host_config: HostConfig) -> Self {
        Self { sandbox, host_config }
    }
}

#[tonic::async_trait]
impl TrustedAgentService for TrustedAgentServiceImpl {
    type StreamStream = ReceiverStream<Result<AgentResponse, Status>>;

    async fn stream(
        &self,
        request: Request<Streaming<AgentRequest>>,
    ) -> Result<Response<Self::StreamStream>, Status> {
        let mut request_stream = request.into_inner();
        let (tx, rx) = tokio::sync::mpsc::channel(RESPONSE_BUFFER_SIZE);

        // Spin up a new Wasm sandbox instance for this stream. It stays alive for
        // the lifetime of the stream and is never shared with other streams.
        let state = HostState::new(self.host_config.clone());
        let mut session = self.sandbox.create_session(state).map_err(|e| {
            Status::internal(format!("failed to instantiate agent sandbox session: {e}"))
        })?;

        // Spawn a background task to handle stream interaction. When the stream ends,
        // the client disconnects or the agent fails, `session` drops, tearing down
        // the Wasm instance.
        tokio::spawn(async move {
            while let Some(request_result) = request_stream.next().await {
                let agent_request = match request_result {
                    Ok(req) => req,
                    Err(e) => {
                        let _ = tx
                            .send(Err(Status::internal(format!(
                                "stream error receiving request: {e}"
                            ))))
                            .await;
                        break;
                    }
                };

                // Errors are not recoverable within the session, so they end the stream.
                let result = match agent_request.request {
                    Some(ProtoRequest::UserMessage(user_msg)) => {
                        // The model and tool backends perform blocking I/O, so the
                        // Wasm step runs on the blocking thread pool. The session is
                        // moved into the task and handed back with the result.
                        let step = tokio::task::spawn_blocking(move || {
                            let result = session.step(&user_msg.text);
                            (session, result)
                        })
                        .await;
                        let (returned_session, result) = match step {
                            Ok(step) => step,
                            Err(e) => {
                                // The session was lost with the panicked task, so the
                                // stream cannot continue.
                                let _ = tx
                                    .send(Err(Status::internal(format!(
                                        "agent step panicked: {e}"
                                    ))))
                                    .await;
                                break;
                            }
                        };
                        session = returned_session;
                        result
                            .map(|text| AgentResponse {
                                response: Some(ProtoResponse::AgentMessage(AgentMessage { text })),
                            })
                            .map_err(|e| Status::internal(format!("agent execution error: {e:#}")))
                    }
                    None => Err(Status::invalid_argument("empty request received")),
                };
                let response = match result {
                    Ok(response) => response,
                    Err(status) => {
                        let _ = tx.send(Err(status)).await;
                        break;
                    }
                };

                if tx.send(Ok(response)).await.is_err() {
                    // Receiver dropped (client closed connection or dropped response stream)
                    break;
                }
            }
        });

        Ok(Response::new(ReceiverStream::new(rx)))
    }
}
