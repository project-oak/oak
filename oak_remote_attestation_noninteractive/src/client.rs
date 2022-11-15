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

use crate::proto::{
    request_wrapper, response_wrapper, streaming_session_client::StreamingSessionClient,
    InvokeRequest, RequestWrapper,
};
use anyhow::Context;
use tonic::transport::Channel;

/// A client that allows interacting with an Oak server instance over gRPC, using the noninteractive
/// remote attestation protocol.
///
/// When sending a message, the client initiates a gRPC stream with the server, which it then uses
/// to fetch the server public key and use that to encrypt the request message, which it then sends
/// over the same stream, in order to ensure that it is processed by the same server throughout.
///
/// It is possible to invoke the [`OakClient::message`] method multiple times, but there is no
/// guarantee that all the invocations will be processed by the same server instance.
pub struct OakClient {
    inner: StreamingSessionClient<Channel>,
}

impl OakClient {
    pub async fn create(uri: &str) -> anyhow::Result<Self> {
        let channel = Channel::from_shared(uri.to_string())
            .context("couldn't create gRPC channel")?
            .connect()
            .await?;
        let inner = StreamingSessionClient::new(channel);
        Ok(Self { inner })
    }
}

impl OakClient {
    pub async fn message(&mut self, body: &[u8]) -> anyhow::Result<Vec<u8>> {
        // TODO(#3442): Fetch the public key from the server, and use it to encrypt the request
        // body.
        let invoke_request = InvokeRequest {
            encrypted_body: body.to_vec(),
        };
        let mut response_stream = self
            .inner
            .stream(futures_util::stream::iter(vec![RequestWrapper {
                request: Some(request_wrapper::Request::InvokeRequest(invoke_request)),
            }]))
            .await
            .context("couldn't send message")?
            .into_inner();
        // Read the next (and only) message from the response stream.
        let response_wrapper = response_stream
            .message()
            .await
            .context("gRPC server error when invoking method")?
            .context("received empty response stream")?;

        let Some(response_wrapper::Response::InvokeResponse(invoke_response)) = response_wrapper.response  else {
            return Err(anyhow::anyhow!("response_wrapper does not have a valid invoke_response message"))
        };

        // TODO(#3442): Decrypt response body. Currently it is not encrypted at all, so we can just
        // return it to the caller.
        Ok(invoke_response.encrypted_body)
    }
}
