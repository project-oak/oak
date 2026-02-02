//
// Copyright 2021 The Project Oak Authors
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
use http::uri::Uri;
use oak_client::{client::OakClient, verifier::AttestationVerifier};
use oak_client_tonic::transport::GrpcStreamingTransport;
use oak_grpc::oak::session::v1::streaming_session_client::StreamingSessionClient;
use prost::Message;
use tonic::transport::Channel;

pub struct OakFunctionsClient {
    oak_client: OakClient<GrpcStreamingTransport>,
}

impl OakFunctionsClient {
    pub async fn new(uri: Uri, verifier: &dyn AttestationVerifier) -> anyhow::Result<Self> {
        let channel =
            Channel::builder(uri).connect().await.context("couldn't connect via gRPC channel")?;
        let mut client = StreamingSessionClient::new(channel);
        let transport = GrpcStreamingTransport::new(|rx| client.stream(rx))
            .await
            .context("couldn't create GRPC streaming transport")?;
        let oak_client =
            OakClient::create(transport, verifier).await.context("couldn't create Oak client")?;
        Ok(Self { oak_client })
    }

    pub async fn invoke(&mut self, request: &[u8]) -> Result<Vec<u8>, micro_rpc::Status> {
        // An error here indicates a failure with gRPC or encoding / decoding.
        let response_bytes = self.oak_client.invoke(request).await.map_err(|err| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                format!("couldn't invoke Oak Functions: {:?}", err),
            )
        })?;
        // An error here is specific to the Oak Functions application (e.g. the Wasm
        // module does not have the correct exported / imported functions).
        let response =
            micro_rpc::ResponseWrapper::decode(response_bytes.as_slice()).map_err(|err| {
                micro_rpc::Status::new_with_message(
                    micro_rpc::StatusCode::Internal,
                    format!("couldn't deserialize response wrapper: {:?}", err),
                )
            })?;
        response.into()
    }
}
