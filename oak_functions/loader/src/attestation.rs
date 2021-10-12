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

use crate::{
    logger::Logger,
    proto::{streaming_session_server::StreamingSession, StreamingRequest, StreamingResponse},
};
use anyhow::Context;
use futures::{Stream, StreamExt};
use log::Level;
use oak_functions_abi::proto::ConfigurationInfo;
use oak_remote_attestation::handshaker::{AttestationBehavior, Encryptor, ServerHandshaker};
use prost::Message;
use std::pin::Pin;
use tonic::{Request, Response, Status, Streaming};

/// Utility structure that receives messages from gRPC streams.
struct Receiver {
    request_stream: Streaming<StreamingRequest>,
}

impl Receiver {
    /// Receives requests from [`Receiver::request_stream`].
    /// Returns `Ok(None)` to indicate that the corresponding gRPC stream has ended.
    async fn receive(&mut self) -> anyhow::Result<Option<StreamingRequest>> {
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
    encryptor: Encryptor,
    /// Handler function that processes data from client requests and creates responses.
    handler: F,
}

impl<F, S> RequestHandler<F, S>
where
    F: Send + Sync + Clone + FnOnce(oak_functions_abi::proto::Request) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync,
{
    pub fn new(encryptor: Encryptor, handler: F) -> Self {
        Self { encryptor, handler }
    }

    /// Decrypts a client request, runs [`RequestHandler::handler`] on them and returns an encrypted
    /// response.
    /// Returns `Ok(None)` to indicate that the corresponding gRPC stream has ended.
    pub async fn handle_request(
        &mut self,
        receiver: &mut Receiver,
    ) -> anyhow::Result<Option<StreamingResponse>> {
        if let Some(encrypted_request) = receiver
            .receive()
            .await
            .context("Couldn't receive request")?
        {
            let decrypted_request = self
                .encryptor
                .decrypt(&encrypted_request.body)
                .context("Couldn't decrypt request")?;

            let response = (self.handler.clone())(oak_functions_abi::proto::Request {
                body: decrypted_request,
            })
            .await?;
            let encrypted_response = self
                .encryptor
                .encrypt(&response)
                .context("Couldn't decrypt response")?;

            Ok(Some(StreamingResponse {
                body: encrypted_response,
            }))
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
    /// Configuration information to provide to the client for the attestation step.
    config_info: ConfigurationInfo,
    /// Logger that is required for logging attestation protocol errors.
    /// Errors are only logged on server side and are not sent to clients.
    logger: Logger,
}

impl<F, S> AttestationServer<F>
where
    F: Send + Sync + Clone + FnOnce(oak_functions_abi::proto::Request) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync,
{
    pub fn create(
        tee_certificate: Vec<u8>,
        request_handler: F,
        config_info: ConfigurationInfo,
        logger: Logger,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            tee_certificate,
            request_handler,
            config_info,
            logger,
        })
    }
}

#[tonic::async_trait]
impl<F, S> StreamingSession for AttestationServer<F>
where
    F: 'static + Send + Sync + Clone + FnOnce(oak_functions_abi::proto::Request) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync + 'static,
{
    type StreamStream =
        Pin<Box<dyn Stream<Item = Result<StreamingResponse, Status>> + Send + Sync + 'static>>;

    async fn stream(
        &self,
        request_stream: Request<tonic::Streaming<StreamingRequest>>,
    ) -> Result<Response<Self::StreamStream>, Status> {
        let tee_certificate = self.tee_certificate.clone();
        let request_handler = self.request_handler.clone();
        let logger = self.logger.clone();

        let request_stream = request_stream.into_inner();
        let mut additional_info = vec![];
        self.config_info
            .encode(&mut additional_info)
            .map_err(|error| {
                log_error(
                    &logger,
                    &format!("Couldn't decode configuration info: {:?}", error),
                );
                Status::aborted("")
            })?;
        let response_stream = async_stream::try_stream! {
            let mut receiver = Receiver { request_stream };

            /// Attest a single gRPC streaming request.
            let mut handshaker = ServerHandshaker::new(
                AttestationBehavior::create_self_attestation(&tee_certificate)
                    .map_err(|error| {
                        log_error(
                            &logger,
                            &format!("Couldn't create self attestation behavior: {:?}", error)
                        );
                        Status::internal("")
                    })?,
                    additional_info,
            );
            while !handshaker.is_completed() {
                let incoming_message = receiver
                    .receive()
                    .await
                    .map_err(|error| {
                        log_error(
                            &logger,
                            &format!("Couldn't receive handshake message: {:?}", error)
                        );
                        Status::aborted("")
                    })?
                    .ok_or_else(|| {
                        log_error(&logger, "Stream stopped preemptively");
                        Status::internal("")
                    })?;

                let outgoing_message = handshaker
                    .next_step(&incoming_message.body)
                    .map_err(|error| {
                        log_error(
                            &logger,
                            &format!("Couldn't process handshake message: {:?}", error)
                        );
                        Status::aborted("")
                    })?;
                if let Some(outgoing_message) = outgoing_message {
                    yield StreamingResponse {
                        body: outgoing_message,
                    };
                }
            }
            let encryptor = handshaker
                .get_encryptor()
                .map_err(|error| {
                    log_error(&logger, &format!("Couldn't get encryptor: {:?}", error));
                    Status::internal("")
                })?;

            let mut handler = RequestHandler::<F, S>::new(encryptor, request_handler);
            while let Some(response) = handler
                .handle_request(&mut receiver)
                .await
                .map_err(|error| {
                    log_error(&logger, &format!("Couldn't handle request: {:?}", error));
                    Status::aborted("")
                })?
            {
                yield response;
            }
        };

        Ok(Response::new(Box::pin(response_stream)))
    }
}

/// Helper function for logging remote attestation errors.
fn log_error(logger: &Logger, error: &str) {
    logger.log_public(
        Level::Warn,
        &format!(
            "{:?}: Remote attestation error: {}",
            std::thread::current().id(),
            error
        ),
    );
}
