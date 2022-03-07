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

//! Server-side implementation of the bidirectional unary gRPC remote attestation handshake
//! protocol.

use crate::proto::{unary_session_server::UnarySession, UnaryRequest, UnaryResponse};
use oak_remote_attestation::handshaker::{AttestationBehavior, Encryptor, ServerHandshaker};
use tonic;

/// Trait for logging error messages.
pub trait LogError {
    fn log_error(&self, error: &str);
}

/// gRPC Attestation Service implementation.
pub struct AttestationServer<F, L> {
    /// PEM encoded X.509 certificate that signs TEE firmware key.
    tee_certificate: Vec<u8>,
    /// Processes data from client requests and creates responses.
    request_handler: F,
    /// Configuration information to provide to the client for the attestation step.
    additional_info: Vec<u8>,
    /// Error logging function that is required for logging attestation protocol errors.
    /// Errors are only logged on server side and are not sent to clients.
    error_logger: L,
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
        Ok(Self {
            tee_certificate,
            request_handler,
            additional_info,
            error_logger,
        })
    }
}

#[tonic::async_trait]
impl<F, S, L> UnarySession for AttestationServer<F, L>
where
    F: 'static + Send + Sync + Clone + FnOnce(Vec<u8>) -> S,
    S: std::future::Future<Output = anyhow::Result<Vec<u8>>> + Send + Sync + 'static,
    L: Send + Sync + Clone + LogError + 'static,
{
    async fn message(
        &self,
        request: tonic::Request<UnaryRequest>,
    ) -> Result<tonic::Response<UnaryResponse>, tonic::Status> {
        let error_logger = self.error_logger.clone();

        error_logger.log_error(&format!(
            "Received unary request, but request handling isn't yet implemented: {:?}",
            request
        ));
        return Err(tonic::Status::aborted(""));
    }
}
