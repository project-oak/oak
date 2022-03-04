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
    streaming_session_client::StreamingSessionClient, StreamingRequest, StreamingResponse,
};
use anyhow::Context;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, ClientHandshaker, Encryptor, ServerIdentityVerifier,
};
use tokio::sync::mpsc::Sender;
use tonic::{transport::Channel, Request, Streaming};

const MESSAGE_BUFFER_SIZE: usize = 1;

/// Convenience structure for sending requests to and receiving responses from the server.
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
        server_verifier: ServerIdentityVerifier,
    ) -> anyhow::Result<Self> {
        let mut channel = GrpcChannel::create(uri)
            .await
            .context("Couldn't create gRPC client")?;
        let encryptor =
            Self::set_up_tunnel(&mut channel, expected_tee_measurement, server_verifier)
                .await
                .context("Couldn't attest server")?;

        Ok(Self { channel, encryptor })
    }

    /// Performs a key exchange handshake and validates the server attestation information to set up
    /// an end-to-end encrypted, attested tunnel to the server.
    async fn set_up_tunnel(
        channel: &mut GrpcChannel,
        expected_tee_measurement: &[u8],
        server_verifier: ServerIdentityVerifier,
    ) -> anyhow::Result<Encryptor> {
        let mut handshaker = ClientHandshaker::new(
            AttestationBehavior::create_peer_attestation(expected_tee_measurement),
            server_verifier,
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

    /// Sends data encrypted by the [`Encryptor`] to the server and decrypts the server responses.
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
