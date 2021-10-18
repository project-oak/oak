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
//

use crate::proto::{
    streaming_session_client::StreamingSessionClient, StreamingRequest, StreamingResponse,
};
use anyhow::Context;
use oak_functions_abi::proto::ConfigurationInfo;
use oak_remote_attestation::{
    handshaker::{AttestationBehavior, ClientHandshaker, Encryptor, ServerIdentityVerifier},
    message::ServerIdentity,
};
use prost::Message;
use tokio::sync::mpsc::Sender;
use tonic::{transport::Channel, Request, Streaming};

pub type ConfigurationVerifier = fn(ConfigurationInfo) -> anyhow::Result<()>;

const MESSAGE_BUFFER_SIZE: usize = 1;

/// Convenience structure for sending requests and receiving responses from the server.
struct GrpcChannel {
    sender: Sender<StreamingRequest>,
    response_stream: Streaming<StreamingResponse>,
}

impl GrpcChannel {
    async fn create(uri: &str) -> anyhow::Result<Self> {
        let channel = Channel::from_shared(uri.to_string())
            .context("Couldn't create gRPC channel")?
            .connect()
            .await
            .context("Couldn't connect via gRPC channel")?;
        let mut client = StreamingSessionClient::new(channel);

        let (sender, mut receiver) = tokio::sync::mpsc::channel(MESSAGE_BUFFER_SIZE);

        let request_stream = async_stream::stream! {
            while let Some(message) = receiver.recv().await {
                yield message;
            }
        };

        let response = client
            .stream(Request::new(request_stream))
            .await
            .context("Couldn't send request")?;
        let response_stream = response.into_inner();

        Ok(Self {
            sender,
            response_stream,
        })
    }

    async fn send(&mut self, request: StreamingRequest) -> anyhow::Result<()> {
        self.sender
            .send(request)
            .await
            .context("Couldn't send request")
    }

    async fn receive(&mut self) -> anyhow::Result<Option<StreamingResponse>> {
        self.response_stream
            .message()
            .await
            .context("Couldn't receive response")
    }
}

/// gRPC Attestation Service client implementation.
pub struct AttestationClient {
    channel: GrpcChannel,
    encryptor: Encryptor,
}

impl AttestationClient {
    pub async fn create(
        uri: &str,
        expected_tee_measurement: &[u8],
        verifier: ConfigurationVerifier,
    ) -> anyhow::Result<Self> {
        let mut channel = GrpcChannel::create(uri)
            .await
            .context("Couldn't create gRPC client")?;
        let encryptor = Self::attest_server(&mut channel, expected_tee_measurement, verifier)
            .await
            .context("Couldn't attest server")?;

        Ok(Self { channel, encryptor })
    }

    /// Attests server for a single gRPC streaming request.
    async fn attest_server(
        channel: &mut GrpcChannel,
        expected_tee_measurement: &[u8],
        config_verifier: ConfigurationVerifier,
    ) -> anyhow::Result<Encryptor> {
        let mut handshaker = ClientHandshaker::new(
            AttestationBehavior::create_peer_attestation(expected_tee_measurement),
            into_server_identity_verifier(config_verifier),
        );
        let client_hello = handshaker
            .create_client_hello()
            .context("Couldn't create client hello message")?;
        channel
            .send(StreamingRequest { body: client_hello })
            .await
            .context("Couldn't send client hello message")?;

        while !handshaker.is_completed() {
            let incoming_message = channel
                .receive()
                .await
                .context("Couldn't receive handshake message")?
                .context("Stream stopped preemptively")?;

            let outgoing_message = handshaker
                .next_step(&incoming_message.body)
                .context("Couldn't process handshake message")?;
            if let Some(outgoing_message) = outgoing_message {
                channel
                    .send(StreamingRequest {
                        body: outgoing_message,
                    })
                    .await
                    .context("Couldn't send handshake message")?;
            }
        }
        let encryptor = handshaker
            .get_encryptor()
            .context("Couldn't get encryptor")?;
        Ok(encryptor)
    }

    /// Sends data encrypted by the [`Encryptor`] to the server and returns server responses.
    /// Returns `Ok(None)` to indicate that the corresponding gRPC stream has ended.
    pub async fn send(
        &mut self,
        request: oak_functions_abi::proto::Request,
    ) -> anyhow::Result<Option<Vec<u8>>> {
        let encrypted_request = self
            .encryptor
            .encrypt(&request.body)
            .context("Couldn't encrypt request")?;
        self.channel
            .send(StreamingRequest {
                body: encrypted_request,
            })
            .await
            .context("Couldn't send encrypted data request")?;

        let encrypted_response = self
            .channel
            .receive()
            .await
            .context("Couldn't send encrypted data request")?;
        let response = match encrypted_response {
            Some(encrypted_response) => {
                let response = self
                    .encryptor
                    .decrypt(&encrypted_response.body)
                    .context("Couldn't decrypt response")?;
                Some(response)
            }
            None => None,
        };

        Ok(response)
    }
}

/// Creates a [`ServerIdentityVerifier`] from the given `ConfigurationVerifier`.
///
/// The `ServerIdentityVerifier` parses the byte array in `server_identity.additional_info` into a
/// `ConfigurationInfo` object. If the conversion is successful, `config_verifier` is invoked to
/// verify the `ConfigurationInfo` object. Otherwise, an error is returned. An error is as well
/// returned if the call to `config_verifier` returns an error.
fn into_server_identity_verifier(config_verifier: ConfigurationVerifier) -> ServerIdentityVerifier {
    let server_verifier = move |server_identity: ServerIdentity| -> anyhow::Result<()> {
        let config = ConfigurationInfo::decode(server_identity.additional_info.as_ref())?;
        // TODO(#2347): Check that ConfigurationInfo does not have additional/unknown fields.
        config_verifier(config)?;
        // TODO(#2316): Verify proof of inclusion in Rekor.
        Ok(())
    };

    Box::new(server_verifier)
}
