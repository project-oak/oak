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

//! Logic for performing remote attestation in multiple sessions

#![no_std]

extern crate alloc;

use alloc::{boxed::Box, sync::Arc, vec::Vec};
use lru::LruCache;
use oak_remote_attestation::handshaker::{AttestationBehavior, Encryptor, ServerHandshaker};

pub type SessionId = [u8; 8];

pub enum SessionState {
    // Boxed due to large size difference, ref: https://rust-lang.github.io/rust-clippy/master/index.html#large_enum_variant
    HandshakeInProgress(Box<ServerHandshaker>),
    EncryptedMessageExchange(Encryptor),
}

/// Maintains remote attestation state for a number of sessions
pub struct SessionTracker {
    /// PEM encoded X.509 certificate that signs TEE firmware key.
    tee_certificate: Vec<u8>,
    /// Configuration information to provide to the client for the attestation step.
    additional_info: Arc<Vec<u8>>,
    known_sessions: LruCache<SessionId, SessionState>,
}

impl SessionTracker {
    pub fn create(cache_size: usize, tee_certificate: Vec<u8>, additional_info: Vec<u8>) -> Self {
        let known_sessions = LruCache::new(cache_size);
        Self {
            tee_certificate,
            additional_info: Arc::new(additional_info),
            known_sessions,
        }
    }

    /// Consumes remote attestation state of an existing session. Creates
    /// initial state if the session is not known.
    ///
    /// Note that getting the remote attestation state of a session always
    /// implicitly removes it from the set of tracked sessions. After
    /// using the state to process a request with this state it must explicitly
    /// be put back into the SessionTracker. This an intentional choice meant
    /// to ensure that faulty state that leads to errors when processing
    /// a request is not persistent.
    pub fn pop_or_create_session_state(
        &mut self,
        session_id: SessionId,
    ) -> anyhow::Result<SessionState> {
        match self.known_sessions.pop(&session_id) {
            None => match AttestationBehavior::create_self_attestation(&self.tee_certificate) {
                Ok(behavior) => Ok(SessionState::HandshakeInProgress(Box::new(
                    ServerHandshaker::new(behavior, self.additional_info.clone()),
                ))),
                Err(error) => Err(error.context("Couldn't create self attestation behavior")),
            },
            Some(SessionState::HandshakeInProgress(handshaker)) => {
                // Completed handshakers are functionally just wrap an
                // encryptor. In that case the underlying handshaker is
                // returned, ensuring consistent state representation.
                match handshaker.is_completed() {
                    false => Ok(SessionState::HandshakeInProgress(handshaker)),
                    true => match handshaker.get_encryptor() {
                        Ok(encryptor) => Ok(SessionState::EncryptedMessageExchange(encryptor)),
                        Err(error) => Err(error.context("Couldn't get encryptor")),
                    },
                }
            }
            Some(SessionState::EncryptedMessageExchange(encryptor)) => {
                Ok(SessionState::EncryptedMessageExchange(encryptor))
            }
        }
    }

    /// Record a session in the tracker. Unlike `pop_or_create_session_state` it does not
    /// normalize session state, instead relying on normalization occuring
    /// at retrieval time.
    pub fn put_session_state(&mut self, session_id: SessionId, session_state: SessionState) {
        self.known_sessions.put(session_id, session_state);
    }
}
