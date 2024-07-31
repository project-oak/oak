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

use anyhow::Context;
use oak_hello_world_proto::oak::containers::example::trusted_application_client::TrustedApplicationClient as GrpcTrustedApplicationClient;
use oak_proto_rust::oak::session::v1::{RequestWrapper, ResponseWrapper};
use tokio::time::Duration;
use tonic::transport::Endpoint;

/// Utility struct used to interface with the launcher
pub struct TrustedApplicationClient {
    inner: GrpcTrustedApplicationClient<tonic::transport::channel::Channel>,
}

impl TrustedApplicationClient {
    pub async fn create(server_addr: String) -> Result<Self, Box<dyn std::error::Error>> {
        let inner: GrpcTrustedApplicationClient<tonic::transport::channel::Channel> = {
            let channel = Endpoint::from_shared(server_addr)
                .context("couldn't form channel")?
                .connect_timeout(Duration::from_secs(120))
                .connect()
                .await
                .context("couldn't connect to trusted app")?;
            GrpcTrustedApplicationClient::new(channel)
        };
        Ok(Self { inner })
    }

    pub async fn session(
        &mut self,
        request: impl tonic::IntoStreamingRequest<Message = RequestWrapper>,
    ) -> anyhow::Result<tonic::Streaming<ResponseWrapper>> {
        Ok(self
            .inner
            // How to safely map this request stream?
            .session(request)
            .await
            .context("couldn't send hello request")?
            .into_inner())
    }
}
