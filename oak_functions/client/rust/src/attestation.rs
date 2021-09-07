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
    attested_invoke_request::RequestType, attested_invoke_response::ResponseType,
    remote_attestation_client::RemoteAttestationClient, AttestedInvokeRequest,
    AttestedInvokeResponse,
};
use anyhow::{anyhow, Context};
use oak_remote_attestation::{
    attestation::{AttestationBehavior, ClientAttestationEngine, Initializing},
    crypto::AeadEncryptor,
};
use tokio::sync::mpsc::Sender;
use tonic::{transport::Channel, Request, Streaming};

const MESSAGE_BUFFER_SIZE: usize = 1;

/// Convenience structure for sending requests and receiving responses from the server.
struct GrpcChannel {
    sender: Sender<AttestedInvokeRequest>,
    response_stream: Streaming<AttestedInvokeResponse>,
}

impl GrpcChannel {
    async fn create(uri: &str) -> anyhow::Result<Self> {
        let channel = Channel::from_shared(uri.to_string())
            .context("Couldn't create gRPC channel")?
            .connect()
            .await
            .context("Couldn't connect via gRPC channel")?;
        let mut client = RemoteAttestationClient::new(channel);

        let (sender, mut receiver) = tokio::sync::mpsc::channel(MESSAGE_BUFFER_SIZE);

        let request_stream = async_stream::stream! {
            while let Some(message) = receiver.recv().await {
                yield message;
            }
        };

        let response = client
            .attested_invoke(Request::new(request_stream))
            .await
            .context("Couldn't send request")?;
        let response_stream = response.into_inner();

        Ok(Self {
            sender,
            response_stream,
        })
    }

    async fn send(&mut self, request: AttestedInvokeRequest) -> anyhow::Result<()> {
        self.sender
            .send(request)
            .await
            .context("Couldn't send request")
    }

    async fn receive(&mut self) -> anyhow::Result<Option<AttestedInvokeResponse>> {
        self.response_stream
            .message()
            .await
            .context("Couldn't receive response")
    }
}

/// gRPC Attestation Service client implementation.
pub struct AttestationClient {
    channel: GrpcChannel,
    encryptor: AeadEncryptor,
}

impl AttestationClient {
    pub async fn create(uri: &str, expected_tee_measurement: &[u8]) -> anyhow::Result<Self> {
        let mut channel = GrpcChannel::create(uri)
            .await
            .context("Couldn't create gRPC client")?;
        let encryptor = Self::attest_server(&mut channel, expected_tee_measurement)
            .await
            .context("Couldn't attest server")?;

        Ok(Self { channel, encryptor })
    }

    /// Attests server for a single gRPC streaming request.
    async fn attest_server(
        channel: &mut GrpcChannel,
        expected_tee_measurement: &[u8],
    ) -> anyhow::Result<AeadEncryptor> {
        let attestation_engine = ClientAttestationEngine::<Initializing>::new(
            AttestationBehavior::create_peer_attestation(expected_tee_measurement)
                .context("Couldn't create peer attestation behavior")?,
        );

        // Send client hello message.
        let (client_hello, attestation_engine) = attestation_engine
            .create_client_hello()
            .context("Couldn't create client hello")?;
        let request = AttestedInvokeRequest {
            request_type: Some(RequestType::ClientHello(client_hello)),
        };
        channel
            .send(request)
            .await
            .context("Couldn't send client hello")?;

        // Receive server attestation identity containing server's ephemeral public key.
        let response = channel
            .receive()
            .await
            .context("Couldn't receive server identity")?
            .context("Stream stopped preemptively")?;
        let response_type = response
            .response_type
            .context("Couldn't read response type")?;
        let server_identity =
            if let ResponseType::ServerIdentity(attestation_response) = response_type {
                Ok(attestation_response)
            } else {
                Err(anyhow!("Received incorrect message type"))
            }?;

        // Remotely attest the server and create:
        // - Client attestation identity containing client's ephemeral public key
        // - Encryptor used for decrypting/encrypting messages between client and server
        let (client_identity, attestation_engine) = attestation_engine
            .process_server_identity(&server_identity)
            .context("Couldn't process server identity")?;
        let request = AttestedInvokeRequest {
            request_type: Some(RequestType::ClientIdentity(client_identity)),
        };
        channel
            .send(request)
            .await
            .context("Couldn't send client identity")?;

        let encryptor = attestation_engine.get_encryptor();
        Ok(encryptor)
    }

    /// Sends data encrypted by the [`AttestationClient::encryptor`] to the server and returns
    /// server responses.
    /// Returns `Ok(None)` to indicate that the corresponding gRPC stream has ended.
    pub async fn send(
        &mut self,
        request: oak_functions_abi::proto::Request,
    ) -> anyhow::Result<Option<Vec<u8>>> {
        let encrypted_message = self
            .encryptor
            .encrypt(&request.body)
            .context("Couldn't encrypt data")?;
        let data_request = AttestedInvokeRequest {
            request_type: Some(RequestType::Request(crate::proto::Request {
                encrypted_payload: Some(encrypted_message),
            })),
        };

        self.channel
            .send(data_request)
            .await
            .context("Couldn't send encrypted data request")?;
        let response = self
            .channel
            .receive()
            .await
            .context("Couldn't send encrypted data request")?;
        let data = if let Some(response) = response {
            let response_type = response
                .response_type
                .context("Couldn't read response type")?;
            let encrypted_payload = if let ResponseType::EncryptedPayload(data) = response_type {
                Ok(data)
            } else {
                Err(anyhow!("Received incorrect message type"))
            }?;
            let payload = self
                .encryptor
                .decrypt(&encrypted_payload)
                .context("Couldn't decrypt data")?;
            Some(payload)
        } else {
            None
        };

        Ok(data)
    }
}
