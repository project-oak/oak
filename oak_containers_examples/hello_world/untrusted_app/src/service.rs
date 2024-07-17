//
// Copyright 2024 The Project Oak Authors
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

use std::{pin::Pin, sync::Arc};

use anyhow::anyhow;
use futures::{Stream, StreamExt};
use oak_containers_launcher::Launcher;
use oak_grpc::oak::session::v1::streaming_session_server::{
    StreamingSession, StreamingSessionServer,
};
use oak_proto_rust::oak::session::v1::{
    request_wrapper, response_wrapper, GetEndorsedEvidenceResponse, InvokeRequest, InvokeResponse,
    RequestWrapper, ResponseWrapper,
};
use tokio::{net::TcpListener, sync::Mutex};
use tokio_stream::wrappers::TcpListenerStream;

use crate::app_client::TrustedApplicationClient;

/// The sample application's implementation of Oak's streaming service protocol.
struct StreamingSessionImpl {
    launcher: Arc<Mutex<Launcher>>,
    trusted_app: Arc<Mutex<TrustedApplicationClient>>,
}

impl StreamingSessionImpl {
    pub fn new(launcher: Launcher, trusted_app: TrustedApplicationClient) -> Self {
        Self {
            launcher: Arc::new(Mutex::new(launcher)),
            trusted_app: Arc::new(Mutex::new(trusted_app)),
        }
    }
}

#[tonic::async_trait]
impl StreamingSession for StreamingSessionImpl {
    type StreamStream =
        Pin<Box<dyn Stream<Item = Result<ResponseWrapper, tonic::Status>> + Send + 'static>>;

    async fn stream(
        &self,
        request: tonic::Request<tonic::Streaming<RequestWrapper>>,
    ) -> Result<tonic::Response<Self::StreamStream>, tonic::Status> {
        let mut request_stream = request.into_inner();

        let launcher = Arc::clone(&self.launcher);
        let trusted_app = Arc::clone(&self.trusted_app);

        let response_stream = async_stream::try_stream! {
            while let Some(request) = request_stream.next().await {
                let request = request
                    .map_err(|err| {
                        tonic::Status::internal(format!("error reading message from request stream: {err}"))
                    })?
                    .request
                    .ok_or_else(|| tonic::Status::invalid_argument("empty request message"))?;

                let response = match request {
                    request_wrapper::Request::GetEndorsedEvidenceRequest(_) => {
                        let endorsed_evidence = {
                            launcher.lock().await.get_endorsed_evidence().await
                            .map_err(|err| tonic::Status::internal(format!("launcher evidence get failed: {err:?}")))?
                        };
                        response_wrapper::Response::GetEndorsedEvidenceResponse(GetEndorsedEvidenceResponse {
                            endorsed_evidence: Some(endorsed_evidence),
                        })
                    }
                    request_wrapper::Request::InvokeRequest(InvokeRequest { encrypted_request }) => {
                        let encrypted_response = trusted_app.lock().await.hello(encrypted_request.expect("empty encrypted request")).await
                            .map_err(|err| tonic::Status::internal(format!("hello failed: {err:?}")))?;
                        response_wrapper::Response::InvokeResponse(
                            InvokeResponse { encrypted_response: Some(encrypted_response) }
                        )
                    }
                };
                yield ResponseWrapper {
                    response: Some(response),
                };
            }
        };

        Ok(tonic::Response::new(Box::pin(response_stream) as Self::StreamStream))
    }
}

pub async fn create(
    listener: TcpListener,
    launcher_args: oak_containers_launcher::Args,
) -> anyhow::Result<()> {
    let mut launcher = oak_containers_launcher::Launcher::create(launcher_args)
        .await
        .map_err(|error| anyhow!("Failed to crate launcher: {error:?}"))?;
    let trusted_app_address = launcher
        .get_trusted_app_address()
        .await
        .map_err(|error| anyhow!("Failed to get app address: {error:?}"))?;
    let app_client = TrustedApplicationClient::create(format!("http://{trusted_app_address}"))
        .await
        .map_err(|error| anyhow!("Failed to create trusted application client: {error:?}"))?;
    tonic::transport::Server::builder()
        .add_service(StreamingSessionServer::new(StreamingSessionImpl::new(launcher, app_client)))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
