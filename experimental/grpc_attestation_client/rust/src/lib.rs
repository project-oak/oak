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

use anyhow::{anyhow, Context};
use oak_attestation_common::{
    crypto::{AeadEncryptor, KeyNegotiator},
    report::AttestationInfo,
};
use oak_grpc_attestation::proto::{
    attested_invoke_request::RequestType, attested_invoke_response::ResponseType,
    remote_attestation_client::RemoteAttestationClient, AttestedInvokeRequest,
    AttestedInvokeResponse, ClientIdentity, SecureRequest,
};
use tokio::sync::mpsc::Sender;
use tonic::{transport::Channel, Request, Streaming};

const MESSAGE_BUFFER_SIZE: usize = 1;

/// Convenience structure for sending requests and receiving responses from the server.
struct Client {
    sender: Sender<AttestedInvokeRequest>,
    response_stream: Streaming<AttestedInvokeResponse>,
}

impl Client {
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

    async fn send(
        &mut self,
        request: AttestedInvokeRequest,
    ) -> anyhow::Result<Option<AttestedInvokeResponse>> {
        self.sender
            .send(request)
            .await
            .context("Couldn't send request")?;
        self.response_stream
            .message()
            .await
            .context("Couldn't receive response")
    }
}

/// gRPC Attestation Service client implementation.
pub struct AttestationClient {
    client: Client,
    encryptor: AeadEncryptor,
}

impl AttestationClient {
    pub async fn create(uri: &str, expected_tee_measurement: &[u8]) -> anyhow::Result<Self> {
        let mut client = Client::create(uri)
            .await
            .context("Couldn't create gRPC client")?;
        let encryptor = AttestationClient::attest(&mut client, expected_tee_measurement)
            .await
            .context("Couldn't attest server")?;

        Ok(Self { client, encryptor })
    }

    /// Attests server for a single gRPC streaming request.
    async fn attest(
        client: &mut Client,
        expected_tee_measurement: &[u8],
    ) -> anyhow::Result<AeadEncryptor> {
        let key_negotiator = KeyNegotiator::create().expect("Couldn't create key negotiator");
        let public_key = key_negotiator
            .public_key()
            .expect("Couldn't get public key");

        // Create attestation request with client's public key.
        let request = AttestedInvokeRequest {
            request_type: Some(RequestType::ClientIdentity(ClientIdentity { public_key })),
        };
        let response = client
            .send(request)
            .await
            .context("Couldn't send attestation request")?
            .context("Stream stopped preemptively")?;

        // Receive server's attestation containing public key.
        let response_type = response
            .response_type
            .context("Couldn't read response type")?;
        let attestation_response =
            if let ResponseType::ServerIdentity(attestation_response) = response_type {
                Ok(attestation_response)
            } else {
                Err(anyhow!("Received incorrect message type"))
            }?;

        // Verify server's attestation info.
        AttestationClient::verify_attestation(
            attestation_response.attestation_info,
            expected_tee_measurement,
        )
        .context("Couldn't verify server attestation")?;

        // Create attestation key based on client's and server's public keys.
        let session_key = key_negotiator
            .derive_session_key(&attestation_response.public_key)
            .context("Couldn't derive session key")?;

        Ok(AeadEncryptor::new(session_key))
    }

    /// Verifies the validity of the attestation info:
    /// - Checks that the TEE report is signed by TEE Provider’s root key.
    /// - Checks that the public key hash from the TEE report is equal to the hash of the public key
    ///   presented in the server response.
    /// - Extracts the TEE measurement from the TEE report and compares it to the
    ///   `expected_tee_measurement`.
    fn verify_attestation(
        attestation_info: Vec<u8>,
        expected_tee_measurement: &[u8],
    ) -> anyhow::Result<()> {
        let serialized_attestation_info =
            String::from_utf8(attestation_info).context("Couldn't get attestation info string")?;
        let deserialized_attestation_info =
            AttestationInfo::from_string(&serialized_attestation_info)
                .context("Couldn't deserialize attestation info")?;

        // TODO(#1867): Add remote attestation support, use real TEE reports and check that
        // `AttestationInfo::certificate` is signed by one of the root certificates.
        deserialized_attestation_info
            .verify()
            .context("Couldn't verify attestation info")?;
        if expected_tee_measurement == deserialized_attestation_info.report.measurement {
            Ok(())
        } else {
            Err(anyhow!("Incorrect TEE measurement"))
        }
    }

    /// Sends data encrypted by the [`AttestationClient::encryptor`] to the server and returns
    /// server responses.
    /// Returns `Ok(None)` to indicate that the corresponding gRPC stream has ended.
    pub async fn send(
        &mut self,
        request: oak_functions_abi::proto::Request,
    ) -> anyhow::Result<Option<Vec<u8>>> {
        let encrypted_payload = self
            .encryptor
            .encrypt(&request.body)
            .context("Couldn't encrypt data")?;
        let data_request = AttestedInvokeRequest {
            request_type: Some(RequestType::Request(SecureRequest { encrypted_payload })),
        };

        let response = self
            .client
            .send(data_request)
            .await
            .context("Couldn't send data request")?;
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
