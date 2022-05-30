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

//! Server-side implementation of the bidirectional gRPC remote attestation handshake
//! protocol.

use crate::proto::{unary_session_server::UnarySession, UnaryRequest, UnaryResponse};
use oak_remote_attestation_sessions::{SessionId, SessionState, SessionTracker};
use oak_utils::LogError;
use std::{convert::TryInto, sync::Mutex};
use tonic;

/// Number of sessions that will be kept in memory.
const SESSIONS_CACHE_SIZE: usize = 10000;

/// gRPC Attestation Service implementation.
pub struct AttestationServer<F, L: LogError> {
    /// Business logic processor, accepts decrypted request and returns responses.
    request_handler: F,
    /// Error logging function that is required for logging attestation protocol errors.
    /// Errors are only logged on server side and are not sent to clients.
    error_logger: L,
    session_tracker: Mutex<SessionTracker>,
}

impl<F, S, L> AttestationServer<F, L>
where
    F: Send + Sync + Clone + FnOnce(Vec<u8>) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync,
    L: Send + Sync + Clone + LogError,
{
    pub fn create(
        tee_certificate: Vec<u8>,
        request_handler: F,
        additional_info: Vec<u8>,
        error_logger: L,
    ) -> anyhow::Result<Self> {
        let session_tracker = Mutex::new(SessionTracker::create(
            SESSIONS_CACHE_SIZE,
            tee_certificate,
            additional_info,
        ));
        Ok(Self {
            request_handler,
            error_logger,
            session_tracker,
        })
    }
}

#[tonic::async_trait]
impl<F, S, L> UnarySession for AttestationServer<F, L>
where
    F: 'static + Send + Sync + Clone + FnOnce(Vec<u8>) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync,
    L: Send + Sync + Clone + LogError + 'static,
{
    async fn message(
        &self,
        request: tonic::Request<UnaryRequest>,
    ) -> anyhow::Result<tonic::Response<UnaryResponse>, tonic::Status> {
        let error_logger = self.error_logger.clone();
        let request_inner = request.into_inner();
        let session_id: SessionId = request_inner.session_id.try_into().map_err(|error| {
            error_logger.log_error(&format!("Received malformed session_id: {:?}", error));
            tonic::Status::invalid_argument("")
        })?;

        let mut session_state = {
            self.session_tracker
                .lock()
                .expect("Couldn't lock session_state mutex")
                .pop_or_create_session_state(session_id)
                .map_err(|error| {
                    error_logger.log_error(&format!("Couldn't pop session state: {:?}", error));
                    tonic::Status::internal("")
                })?
        };

        let response_body = match session_state {
            SessionState::HandshakeInProgress(ref mut handshaker) => {
                handshaker
                    .next_step(&request_inner.body)
                    .map_err(|error| {
                        error_logger
                            .log_error(&format!("Couldn't process handshake message: {:?}", error));
                        tonic::Status::aborted("")
                    })?
                    // After receiving a valid `ClientIdentity` message
                    // (the last step of the key exchange)
                    // ServerHandshaker.next_step returns `None`. For unary
                    // request we do want to send an explicit confirmation in
                    // the form of a status message. Hence in case of `None`
                    // fallback to a default (empty) response.
                    .unwrap_or_default()
            }
            SessionState::EncryptedMessageExchange(ref mut encryptor) => {
                let decrypted_request =
                    encryptor.decrypt(&request_inner.body).map_err(|error| {
                        error_logger.log_error(&format!("Couldn't decrypt request: {:?}", error));
                        tonic::Status::aborted("")
                    })?;

                let response = (self.request_handler.clone())(decrypted_request)
                    .await
                    .map_err(|error| {
                        error_logger.log_error(&format!("Couldn't handle request: {:?}", error));
                        tonic::Status::aborted("")
                    })?;

                encryptor.encrypt(&response).map_err(|error| {
                    error_logger.log_error(&format!("Couldn't encrypt response: {:?}", error));
                    tonic::Status::aborted("")
                })?
            }
        };

        // Note that we only get here if no errors occured during the preceding
        // steps. If errors do occur the session state as tracked by the server
        // is effectively erased. This allows the client to negotiate a new
        // handshake.
        self.session_tracker
            .lock()
            .expect("Couldn't lock session_state mutex")
            .put_session_state(session_id, session_state);
        Ok(tonic::Response::new(UnaryResponse {
            body: response_body,
        }))
    }
}
