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

use async_trait::async_trait;
use oak_remote_attestation_sessions::SessionId;
use oak_remote_attestation_sessions_client::AttestationTransport;

/// gRPC implementation of [`AttestationTransport`] trait using a bidi gRPC stream.
pub struct StreamingGrpcClient {}

impl StreamingGrpcClient {
    pub async fn create(_uri: &str) -> anyhow::Result<Self> {
        // TODO(#3191): Implement streaming attestation.
        std::unimplemented!("StreamingGrpcClient not yet implemented")
    }
}

// Async trait requires the definition and all implementations to be marked as
// optionally [`Send`] if one implementation is not.
#[async_trait(?Send)]
impl AttestationTransport for StreamingGrpcClient {
    async fn message(&mut self, _session_id: SessionId, _body: Vec<u8>) -> anyhow::Result<Vec<u8>> {
        // TODO(#3191): Implement streaming attestation.
        std::unimplemented!("StreamingGrpcClient not yet implemented")
    }
}
