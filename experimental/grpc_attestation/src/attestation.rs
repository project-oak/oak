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
    remote_attestation_server::RemoteAttestation, AttestedInvokeRequest, AttestedInvokeResponse,
    ServerIdentity,
};
use anyhow::{anyhow, Context};
use futures::{Stream, StreamExt};
use log::warn;
use oak_attestation_common::{
    crypto::{AeadEncryptor, KeyNegotiator},
    get_sha256,
    report::{AttestationInfo, Report},
};
use std::pin::Pin;
use tonic::{Request, Response, Status, Streaming};

/// Utility structure that receives messages from gRPC streams.
struct Receiver {
    request_stream: Streaming<AttestedInvokeRequest>,
}

impl Receiver {
    /// Receives requests from [`Receiver::request_stream`].
    /// Returns `Ok(None)` to indicate that the corresponding gRPC stream has ended.
    async fn receive(&mut self) -> anyhow::Result<Option<AttestedInvokeRequest>> {
        let request = if let Some(request) = self.request_stream.next().await {
            Some(request.context("Couldn't receive request")?)
        } else {
            None
        };
        Ok(request)
    }
}

struct RequestHandler<F, S>
where
    F: Send + Sync + Clone + FnOnce(Vec<u8>) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync,
{
    /// Utility object for decrypting and encrypting messages using a Diffie-Hellman session key.
    encryptor: AeadEncryptor,
    /// Handler function that processes data from client requests and creates responses.
    handler: F,
}

impl<F, S> RequestHandler<F, S>
where
    F: Send + Sync + Clone + FnOnce(Vec<u8>) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync,
{
    pub fn new(encryptor: AeadEncryptor, handler: F) -> Self {
        Self { encryptor, handler }
    }

    /// Decrypts a client request, runs [`RequestHandler::handler`] on them and returns an encrypted
    /// response.
    /// Returns `Ok(None)` to indicate that the corresponding gRPC stream has ended.
    pub async fn handle_request(
        &mut self,
        receiver: &mut Receiver,
    ) -> anyhow::Result<Option<AttestedInvokeResponse>> {
        if let Some(request) = receiver
            .receive()
            .await
            .context("Couldn't receive request")?
        {
            let request_type = request.request_type.context("Couldn't read request type")?;
            let encrypted_request_payload =
                if let RequestType::Request(request) = request_type {
                    Ok(request.encrypted_payload)
                } else {
                    Err(anyhow!("Received incorrect message type"))
                }?;
            let request_payload = self
                .encryptor
                .decrypt(&encrypted_request_payload)
                .context("Couldn't decrypt data")?;

            let response_payload = (self.handler.clone())(request_payload).await?;
            let encrypted_response_payload = self
                .encryptor
                .encrypt(&response_payload)
                .context("Couldn't encrypt data")?;
            let response = AttestedInvokeResponse {
                response_type: Some(ResponseType::EncryptedPayload(encrypted_response_payload)),
            };

            Ok(Some(response))
        } else {
            Ok(None)
        }
    }
}

/// gRPC Attestation Service implementation.
pub struct AttestationServer<F> {
    /// PEM encoded X.509 certificate that signs TEE firmware key.
    tee_certificate: Vec<u8>,
    /// Processes data from client requests and creates responses.
    request_handler: F,
}

impl<F, S> AttestationServer<F>
where
    F: Send + Sync + Clone + FnOnce(Vec<u8>) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync,
{
    pub fn create(tee_certificate: Vec<u8>, request_handler: F) -> anyhow::Result<Self> {
        Ok(Self {
            tee_certificate,
            request_handler,
        })
    }

    /// Attest a single gRPC streaming request. Client messages are provided via `receiver`.
    async fn attest(
        receiver: &mut Receiver,
        tee_certificate: Vec<u8>,
    ) -> anyhow::Result<(AttestedInvokeResponse, AeadEncryptor)> {
        let request = receiver
            .receive()
            .await
            .context("Couldn't receive attestation request")?
            .context("Stream stopped preemptively")?;

        // Receive client's attestation request containing a public key.
        // TODO(#2103): Refactor gRPC Attestation protocol state machine.
        let request_type = request.request_type.context("Couldn't read request type")?;
        let request = if let RequestType::ClientIdentity(request) = request_type {
            Ok(request)
        } else {
            Err(anyhow!("Received incorrect message type"))
        }?;

        // Generate session key.
        let key_negotiator = KeyNegotiator::create().context("Couldn't create key negotiator")?;
        let public_key = key_negotiator
            .public_key()
            .context("Couldn't get public key")?;
        let session_key = key_negotiator
            .derive_session_key(&request.public_key)
            .context("Couldn't derive session key")?;

        let encryptor = AeadEncryptor::new(session_key);

        // Generate attestation info with a TEE report.
        // TEE report contains a hash of the server's public key.
        let public_key_hash = get_sha256(&public_key);
        let tee_report = Report::new(&public_key_hash);
        let attestation_info = AttestationInfo {
            report: tee_report,
            certificate: tee_certificate,
        };
        let serialized_attestation_info = attestation_info
            .to_string()
            .context("Couldn't serialize attestation info")?;

        let attestation_response = AttestedInvokeResponse {
            response_type: Some(ResponseType::ServerIdentity(ServerIdentity {
                public_key,
                attestation_info: serialized_attestation_info.as_bytes().to_vec(),
            })),
        };

        Ok((attestation_response, encryptor))
    }
}

#[tonic::async_trait]
impl<F, S> RemoteAttestation for AttestationServer<F>
where
    F: 'static + Send + Sync + Clone + FnOnce(Vec<u8>) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync + 'static,
{
    type AttestedInvokeStream =
        Pin<Box<dyn Stream<Item = Result<AttestedInvokeResponse, Status>> + Send + Sync + 'static>>;

    async fn attested_invoke(
        &self,
        request_stream: Request<tonic::Streaming<AttestedInvokeRequest>>,
    ) -> Result<Response<Self::AttestedInvokeStream>, Status> {
        let tee_certificate = self.tee_certificate.clone();
        let request_handler = self.request_handler.clone();

        let request_stream = request_stream.into_inner();
        let response_stream = async_stream::try_stream! {
            let mut receiver = Receiver { request_stream };
            let (attestation_response, encryptor) = Self::attest(&mut receiver, tee_certificate)
                .await
                .map_err(|error| {
                    let message = format!("Couldn't attest to the client: {:?}", error).to_string();
                    warn!("{}", message);
                    Status::internal(message)
                })?;
            yield attestation_response;

            let mut handler = RequestHandler::<F, S>::new(encryptor, request_handler);
            while let Some(response) = handler.handle_request(&mut receiver).await.map_err(|error| {
                let message = format!("Couldn't handle request: {:?}", error);
                warn!("{}", message);
                Status::internal(message)
            })? {
                yield response;
            }
        };

        Ok(Response::new(Box::pin(response_stream)))
    }
}
