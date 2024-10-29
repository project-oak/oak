//
// Copyright 2024 The Project Oak Authors
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

mod session_helpers;

use micro_rpc_noise_rust_proto::oak::containers::example::TrustedApplication;
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ServerSession,
    Session,
};

use crate::session_helpers::ServerSessionHelpers;

/// A simple single-session implementation of the service.
pub struct TrustedApplicationService {
    server_session: ServerSession,
}

impl TrustedApplicationService {
    pub fn new() -> Self {
        let server_session = ServerSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .expect("Failed to create server session");
        Self { server_session }
    }
}

impl Default for TrustedApplicationService {
    fn default() -> Self {
        Self::new()
    }
}

macro_rules! micro_rpc_err {
    ($($args:tt)*) => {
        micro_rpc::Status::new_with_message(micro_rpc::StatusCode::Internal, format!($($args)*))
    }
}

impl TrustedApplication for TrustedApplicationService {
    fn oak_session(
        &mut self,
        request: SessionRequest,
    ) -> Result<SessionResponse, micro_rpc::Status> {
        if self.server_session.is_open() {
            let bytes = self
                .server_session
                .decrypt_request(&request)
                .map_err(|e| micro_rpc_err!("Failed to decrypt: {e}"))?;
            let response = micro_rpc_noise_application::handle(&bytes)
                .map_err(|e| micro_rpc_err!("Application failed: {e}"))?;
            let encrypted_response = self
                .server_session
                .encrypt_response(&response)
                .map_err(|e| micro_rpc_err!("Failed to encrypt: {e}"))?;
            Ok(encrypted_response)
        } else {
            let response = self
                .server_session
                .init_session(&request)
                .map_err(|e| micro_rpc_err!("Init message handling failed: {e}"))?;

            match response {
                Some(response) => Ok(response),
                None => panic!("what do do?"),
            }
        }
    }
}
