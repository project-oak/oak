//
// Copyright 2022 The Project Oak Authors
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

use crate::proto::{unary_session_client::UnarySessionClient, UnaryRequest};
use anyhow::Context;
use async_trait::async_trait;
use oak_remote_attestation_sessions::SessionId;
use oak_remote_attestation_sessions_client::UnaryClient;
use tonic::transport::Channel;

/// gRPC implementation of of [`UnaryClient`]. Serves as an inner of the
/// public [`AttestationClient`].
pub struct GrpcClient {
    inner: UnarySessionClient<Channel>,
}

impl GrpcClient {
    pub async fn create(uri: &str) -> anyhow::Result<Self> {
        let channel = Channel::from_shared(uri.to_string())
            .context("Couldn't create gRPC channel")?
            .connect()
            .await?;
        let inner = UnarySessionClient::new(channel);
        Ok(Self { inner })
    }
}

// Async trait requires the definition and all implementations to be marked as
// optionally [`Send`] if one implementation is not.
#[async_trait(?Send)]
impl UnaryClient for GrpcClient {
    async fn message(&mut self, session_id: SessionId, body: Vec<u8>) -> anyhow::Result<Vec<u8>> {
        let response = self
            .inner
            .message(UnaryRequest {
                body,
                session_id: session_id.to_vec(),
            })
            .await
            .context("Couldn't send message")?
            .into_inner()
            .body;

        Ok(response)
    }
}
