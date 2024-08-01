//
// Copyright 2023 The Project Oak Authors
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

/// App service shows an example of the boilerplate needed to implement the
/// Oak-related machinery for session message stream handling.
///
/// Oak doesn't provide full service implementation conveniences in the SDK,
/// since typically, Oak-enabled methods will be part of a larger service that
/// may need to be configured in specific ways.
use std::sync::Arc;

use anyhow::anyhow;
use oak_containers_sdk::OakSessionContext;
use oak_hello_world_proto::oak::containers::example::trusted_application_server::{
    TrustedApplication, TrustedApplicationServer,
};
use oak_proto_rust::oak::session::v1::RequestWrapper;
use tokio::net::TcpListener;
use tokio_stream::wrappers::TcpListenerStream;

/// The struct that will hold the gRPC TrustedApplication implementation.
struct TrustedApplicationImplementation {
    oak_session_context: Arc<OakSessionContext>,
}

impl TrustedApplicationImplementation {
    pub fn new(oak_session_context: OakSessionContext) -> Self {
        Self { oak_session_context: Arc::new(oak_session_context) }
    }
}

#[tonic::async_trait]
impl TrustedApplication for TrustedApplicationImplementation {
    type SessionStream = oak_containers_sdk::tonic::OakSessionStream;

    async fn session(
        &self,
        request: tonic::Request<tonic::Streaming<RequestWrapper>>,
    ) -> Result<tonic::Response<Self::SessionStream>, tonic::Status> {
        oak_containers_sdk::tonic::oak_session(self.oak_session_context.clone(), request).await
    }
}

pub async fn create(
    listener: TcpListener,
    oak_session_context: OakSessionContext,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(TrustedApplicationServer::new(TrustedApplicationImplementation::new(
            oak_session_context,
        )))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
