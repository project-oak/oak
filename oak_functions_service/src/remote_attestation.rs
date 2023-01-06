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

//! Server-side implementation the remote attestation handshake protocol.
//!
//! A simplified version of the implementation from the `oak_grpc_unary_attestation`
//! crate.
//!
//! TODO(#2741): Refactor this to share more code between the two runtimes.

extern crate alloc;

use alloc::{sync::Arc, vec::Vec};
use oak_remote_attestation::handshaker::AttestationGenerator;

/// Information about a public key.
#[derive(Debug, Clone)]
pub struct PublicKeyInfo {
    /// The serialized public key.
    pub public_key: Vec<u8>,
    /// The serialized attestation report that binds the public key to the specific version of the
    /// code running in a TEE.
    pub attestation: Vec<u8>,
}

pub trait Handler {
    fn handle(&mut self, request: &[u8]) -> anyhow::Result<Vec<u8>>;
}

pub trait AttestationHandler {
    fn message(&mut self, body: &[u8]) -> anyhow::Result<Vec<u8>>;
    fn get_public_key_info(&self) -> PublicKeyInfo;
}

pub struct AttestationSessionHandler<H: Handler> {
    // TODO(#3442): Use attestation generator to attest to the public key.
    _attestation_generator: Arc<dyn AttestationGenerator>,
    request_handler: H,
}

impl<H: Handler> AttestationSessionHandler<H> {
    pub fn create(
        attestation_generator: Arc<dyn AttestationGenerator>,
        request_handler: H,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            _attestation_generator: attestation_generator,
            request_handler,
        })
    }
}

impl<H: Handler> AttestationHandler for AttestationSessionHandler<H> {
    fn message(&mut self, body: &[u8]) -> anyhow::Result<Vec<u8>> {
        // TODO(#3442): Decrypt request (currently not encrypted).
        let decrypted_request = body;
        let response = self.request_handler.handle(decrypted_request)?;
        // TODO(#3442): Encrypt response.
        let encrypted_response = response;
        Ok(encrypted_response)
    }

    fn get_public_key_info(&self) -> PublicKeyInfo {
        // TODO(#3442): Generate and return public key.
        PublicKeyInfo {
            public_key: Vec::new(),
            attestation: Vec::new(),
        }
    }
}
