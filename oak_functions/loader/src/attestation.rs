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
    remote_attestation_server::RemoteAttestation, AttestationMessage, AttestedInvokeRequest,
    AttestedInvokeResponse,
};
use anyhow::{anyhow, Context};
use futures::{Stream, StreamExt};
use log::warn;
use oak_remote_attestation::{
    attestation::{AttestationBehavior, Attesting, Initializing, ServerAttestationEngine},
    crypto::AeadEncryptor,
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
    F: Send + Sync + Clone + FnOnce(oak_functions_abi::proto::Request) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync,
{
    /// Utility object for decrypting and encrypting messages using a Diffie-Hellman session key.
    encryptor: AeadEncryptor,
    /// Handler function that processes data from client requests and creates responses.
    handler: F,
}

impl<F, S> RequestHandler<F, S>
where
    F: Send + Sync + Clone + FnOnce(oak_functions_abi::proto::Request) -> S,
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
            let secure_request = if let RequestType::Request(request) = request_type {
                Ok(request)
            } else {
                Err(anyhow!("Received incorrect message type"))
            }?;
            let request_payload = self
                .encryptor
                .decrypt(
                    &secure_request
                        .encrypted_payload
                        .context("Empty encrypted payload")?,
                )
                .context("Couldn't decrypt data")?;

            let request = oak_functions_abi::proto::Request {
                body: request_payload,
            };

            let response_payload = (self.handler.clone())(request).await?;
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
    F: Send + Sync + Clone + FnOnce(oak_functions_abi::proto::Request) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync,
{
    pub fn create(tee_certificate: Vec<u8>, request_handler: F) -> anyhow::Result<Self> {
        Ok(Self {
            tee_certificate,
            request_handler,
        })
    }
}

#[tonic::async_trait]
impl<F, S> RemoteAttestation for AttestationServer<F>
where
    F: 'static + Send + Sync + Clone + FnOnce(oak_functions_abi::proto::Request) -> S,
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

            let (attestation_response, attestation_engine) = process_client_hello(&mut receiver, &tee_certificate)
                .await
                .map_err(|error| {
                    let message = format!("Couldn't process client hello: {:?}", error).to_string();
                    warn!("{}", message);
                    Status::internal(message)
                })?;
            yield attestation_response;

            let encryptor = process_client_identity(&mut receiver, attestation_engine)
                .await
                .map_err(|error| {
                    let message = format!("Couldn't process client identity: {:?}", error).to_string();
                    warn!("{}", message);
                    Status::internal(message)
                })?;

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

/// Attest a single gRPC streaming request. Client messages are provided via `receiver`.
async fn process_client_hello(
    receiver: &mut Receiver,
    tee_certificate: &[u8],
) -> anyhow::Result<(AttestedInvokeResponse, ServerAttestationEngine<Attesting>)> {
    let request = receiver
        .receive()
        .await
        .context("Couldn't receive attestation request")?
        .context("Stream stopped preemptively")?;

    // Receive client hello message.
    let request_type = request.request_type.context("Couldn't read request type")?;
    let client_hello = if let RequestType::AttestationMessage(request) = request_type {
        request.body
    } else {
        anyhow::bail!("Received incorrect message type");
    };

    let attestation_engine = ServerAttestationEngine::<Initializing>::new(
        AttestationBehavior::create_self_attestation(tee_certificate)
            .context("Couldn't create self attestation behavior")?,
    );
    let (server_identity, attestation_engine) = attestation_engine
        .process_client_hello(&client_hello)
        .context("Couldn't accept client hello")?;

    // Create server attestation identity.
    let attestation_response = AttestedInvokeResponse {
        response_type: Some(ResponseType::AttestationMessage(AttestationMessage {
            body: server_identity,
        })),
    };
    Ok((attestation_response, attestation_engine))
}

/// Attest a single gRPC streaming request. Client messages are provided via `receiver`.
async fn process_client_identity(
    receiver: &mut Receiver,
    attestation_engine: ServerAttestationEngine<Attesting>,
) -> anyhow::Result<AeadEncryptor> {
    let request = receiver
        .receive()
        .await
        .context("Couldn't receive attestation request")?
        .context("Stream stopped preemptively")?;

    // Receive client attestation identity.
    let request_type = request.request_type.context("Couldn't read request type")?;
    let client_identity = if let RequestType::AttestationMessage(request) = request_type {
        request.body
    } else {
        anyhow::bail!("Received incorrect message type");
    };

    let attestation_engine = attestation_engine
        .process_client_identity(&client_identity)
        .context("Couldn't attest the client")?;
    let encryptor = attestation_engine.get_encryptor();
    Ok(encryptor)
}
