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
//! A simplified version of the implementation from the `grpc_attestation`
//! crate. TODO(#2741): Refactor this to share more code between the two runtimes.

extern crate alloc;

use alloc::{sync::Arc, vec::Vec};
use anyhow::Context;
use oak_remote_attestation::{
    crypto::Signer,
    handshaker::{AttestationBehavior, AttestationGenerator, AttestationVerifier},
};
use oak_remote_attestation_sessions::{SessionId, SessionState, SessionTracker};

/// Number of sessions that will be kept in memory.
const SESSIONS_CACHE_SIZE: usize = 10000;

/// Information about a public key.
#[derive(Debug, Clone)]
pub struct PublicKeyInfo {
    /// The serialized public key.
    pub public_key: Vec<u8>,
    /// The serialized attestation report that binds the public key to the specific version of the
    /// code running in a TEE.
    pub attestation: Vec<u8>,
}

pub trait AttestationHandler {
    fn message(&mut self, session_id: SessionId, body: &[u8]) -> anyhow::Result<Vec<u8>>;
    fn get_public_key_info(&self) -> PublicKeyInfo;
}

pub struct AttestationSessionHandler<F, G: AttestationGenerator, V: AttestationVerifier> {
    session_tracker: SessionTracker<G, V>,
    request_handler: F,
    public_key_info: PublicKeyInfo,
}

impl<F, G: AttestationGenerator, V: AttestationVerifier> AttestationSessionHandler<F, G, V>
where
    F: Send + Sync + Clone + FnOnce(Vec<u8>) -> anyhow::Result<Vec<u8>>,
{
    pub fn create(
        request_handler: F,
        attestation_behavior: AttestationBehavior<G, V>,
    ) -> anyhow::Result<Self> {
        let signer = Arc::new(Signer::create().context("Couldn't create signer")?);
        let public_key = signer
            .public_key()
            .context("Couldn't get public key")?
            .to_vec();
        let attestation = attestation_behavior
            .generator
            .generate_attestation(&public_key)
            .context("Couldn't generate attestation")?;
        let public_key_info = PublicKeyInfo {
            public_key,
            attestation,
        };
        let session_tracker =
            SessionTracker::create(SESSIONS_CACHE_SIZE, attestation_behavior, signer);

        Ok(Self {
            session_tracker,
            request_handler,
            public_key_info,
        })
    }
}

impl<F, G: AttestationGenerator, V: AttestationVerifier> AttestationHandler
    for AttestationSessionHandler<F, G, V>
where
    F: Send + Sync + Clone + FnOnce(Vec<u8>) -> anyhow::Result<Vec<u8>>,
    G: AttestationGenerator,
    V: AttestationVerifier,
{
    fn message(&mut self, session_id: SessionId, body: &[u8]) -> anyhow::Result<Vec<u8>> {
        let mut session_state = {
            self.session_tracker
                .pop_or_create_session_state(session_id)
                .expect("Couldn't pop session state")
        };
        let response_body = match session_state {
            SessionState::HandshakeInProgress(ref mut handshaker) => {
                handshaker
                    .next_step(body)
                    .context("Couldn't process handshake message")?
                    // After receiving a valid `ClientIdentity` message
                    // (the last step of the key exchange)
                    // ServerHandshaker.next_step returns `None`. For unary
                    // request we do want to send an explicit confirmation in
                    // the form of a status message. Hence in case of `None`
                    // fallback to a default (empty) response.
                    .unwrap_or_default()
            }
            SessionState::EncryptedMessageExchange(ref mut encryptor) => {
                let decrypted_request = encryptor
                    .decrypt(body)
                    .context("Couldn't decrypt response")?;

                let response = (self.request_handler.clone())(decrypted_request)?;

                encryptor
                    .encrypt(&response)
                    .context("Couldn't encrypt response")?
            }
        };

        self.session_tracker
            .put_session_state(session_id, session_state);

        Ok(response_body)
    }

    fn get_public_key_info(&self) -> PublicKeyInfo {
        self.public_key_info.clone()
    }
}
