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
    grpc::{BackendConnection, PredictRequest, PredictionServiceClient},
    proto::{streaming_session_server::StreamingSession, StreamingRequest, StreamingResponse},
};
use anyhow::Context;
use futures::{task::Poll, Stream, StreamExt};
use log::warn;
use oak_functions_abi::proto::ConfigurationInfo;
use oak_remote_attestation::handshaker::{AttestationBehavior, Encryptor, ServerHandshaker};
use pin_project_lite::pin_project;
use prost::Message;
use std::{future::Future, pin::Pin};
use sync_wrapper::SyncWrapper;
use tonic::{transport::Channel, Request, Response, Status, Streaming};

struct RequestHandler {
    encryptor: Encryptor,
    client: PredictionServiceClient<Channel>,
}

impl RequestHandler {
    fn new(encryptor: Encryptor, client: PredictionServiceClient<Channel>) -> Self {
        Self { encryptor, client }
    }

    /// Decrypts a client request, forwards it to the prediction service, encrypts the resopnse and
    /// sends it back to the client.
    ///
    /// Returns `Ok(None)` to indicate that the corresponding gRPC stream has ended.
    async fn handle_request(
        &mut self,
        request_stream: &mut Streaming<StreamingRequest>,
    ) -> anyhow::Result<Option<StreamingResponse>> {
        if let Some(encrypted_request) = request_stream.next().await {
            let encrypted_request = encrypted_request.context("Couldn't receive request")?;
            let decrypted_request = self
                .encryptor
                .decrypt(&encrypted_request.body)
                .context("couldn't decrypt request")?;

            let predict_request = PredictRequest::decode(&*decrypted_request)
                .context("couldn't parse decrypted request")?;
            let mut client = self.client.clone();
            // Wrap the gRPC client call to make it `Sync`.
            let sync_predict = FutureSyncWrapper {
                inner: SyncWrapper::new(client.predict(predict_request)),
            };
            let response = sync_predict
                .await
                .context("couldn't execute prediction")?
                .into_inner();

            let wrapped_response = oak_functions_abi::proto::Response::create(
                oak_functions_abi::proto::StatusCode::Success,
                response.encode_to_vec(),
            );
            let encrypted_response = self
                .encryptor
                .encrypt(&wrapped_response.encode_to_vec())
                .context("couldn't encrypt response")?;

            Ok(Some(StreamingResponse {
                body: encrypted_response,
            }))
        } else {
            Ok(None)
        }
    }
}

pin_project! {
    /// Utility wrapper to implement `Sync` for `Future`s by wrapping the inner Future in a
    /// `SyncWrapper`.
    struct FutureSyncWrapper<F> {
        #[pin]
        inner: SyncWrapper<F>,
    }
}

impl<F: Future> Future for FutureSyncWrapper<F> {
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context) -> Poll<Self::Output> {
        self.project().inner.get_pin_mut().poll(cx)
    }
}

/// gRPC Attestation Service implementation.
pub struct AttestationServer {
    /// PEM encoded X.509 certificate that signs TEE firmware key.
    tee_certificate: Vec<u8>,
    /// gRPC connection to the predictions service.
    connection: BackendConnection,
}

impl AttestationServer {
    pub fn create(tee_certificate: Vec<u8>, connection: BackendConnection) -> anyhow::Result<Self> {
        Ok(Self {
            tee_certificate,
            connection,
        })
    }
}

#[tonic::async_trait]
impl StreamingSession for AttestationServer {
    type StreamStream =
        Pin<Box<dyn Stream<Item = Result<StreamingResponse, Status>> + Send + Sync + 'static>>;

    async fn stream(
        &self,
        request_stream: Request<Streaming<StreamingRequest>>,
    ) -> Result<Response<Self::StreamStream>, Status> {
        let tee_certificate = self.tee_certificate.clone();
        // Create fake configuration info for now, as it cannot be empty for the attestation
        // handshake.
        // TODO(#2420): Remove once Java client can work without the configuration info.
        let additional_info = ConfigurationInfo {
            wasm_hash: vec![0, 1, 2, 3],
            policy: None,
            ml_inference: false,
            metrics: None,
        }
        .encode_to_vec();
        let client = self.connection.create_client();
        let response_stream = async_stream::try_stream! {
            let mut request_stream = request_stream.into_inner();
            // Perform attestation and key exchange.
            let mut handshaker = ServerHandshaker::new(
                AttestationBehavior::create_self_attestation(&tee_certificate)
                    .map_err(|error| {
                        warn!("Couldn't create self attestation behavior: {:?}", error);
                        Status::internal("")
                    })?,
                    additional_info,
            );
            while !handshaker.is_completed() {
                let incoming_message = request_stream.next()
                    .await
                    .ok_or_else(|| {
                        warn!("Stream stopped preemptively");
                        Status::internal("")
                    })?
                    .map_err(|error| {
                        warn!("Couldn't get next message: {:?}", error);
                        Status::internal("")
                    })?;

                let outgoing_message = handshaker
                    .next_step(&incoming_message.body)
                    .map_err(|error| {
                        warn!("Couldn't process handshake message: {:?}", error);
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
                    warn!("Couldn't get encryptor: {:?}", error);
                    Status::internal("")
                })?;

            // Handle subsequent messages on the stream.
            let mut handler = RequestHandler::new(encryptor, client);
            while let Some(response) = handler
                .handle_request(&mut request_stream)
                .await
                .map_err(|error| {
                    warn!("Couldn't handle request: {:?}", error);
                    Status::aborted("")
                })?
            {
                yield response;
            }
        };

        Ok(Response::new(Box::pin(response_stream)))
    }
}
