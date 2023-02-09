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
//

use crate::proto::streaming_session_client::StreamingSessionClient;
use tonic::transport::Channel;

pub trait AsyncTransport {
    // TODO(#3643): Make transport async and update the Rust version to support this.
    fn invoke(&mut self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>>;
}

pub struct GrpcStreamingTransport {
    _rpc_client: StreamingSessionClient<Channel>,
}

impl GrpcStreamingTransport {
    pub fn new(rpc_client: StreamingSessionClient<Channel>) -> Self {
        Self { _rpc_client: rpc_client }
    }
}

impl AsyncTransport for GrpcStreamingTransport {
    // TODO(#3643): Implement gRPC Rust client.
    fn invoke(&mut self, _request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        Ok(vec![])
    }
}
