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

use alloc::boxed::Box;
use lru::LruCache;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, AttestationGenerator, AttestationVerifier, Encryptor, ServerHandshaker,
};

pub const SESSION_ID_LENGTH: usize = 8;
pub type SessionId = [u8; SESSION_ID_LENGTH];

pub enum SessionState<G: AttestationGenerator, V: AttestationVerifier> {
    // Boxed due to large size difference, ref: https://rust-lang.github.io/rust-clippy/master/index.html#large_enum_variant
    HandshakeInProgress(Box<ServerHandshaker<G, V>>),
    EncryptedMessageExchange(Encryptor),
}

/// Maintains remote attestation state for a number of sessions
pub struct SessionTracker<G: AttestationGenerator, V: AttestationVerifier> {
    attestation_behavior: AttestationBehavior<G, V>,
    known_sessions: LruCache<SessionId, SessionState<G, V>>,
}

impl<G: AttestationGenerator, V: AttestationVerifier> SessionTracker<G, V> {
    pub fn create(cache_size: usize, attestation_behavior: AttestationBehavior<G, V>) -> Self {
        let known_sessions = LruCache::new(cache_size);
        Self {
            attestation_behavior,
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
    ) -> anyhow::Result<SessionState<G, V>> {
        match self.known_sessions.pop(&session_id) {
            None => Ok(SessionState::HandshakeInProgress(Box::new(
                ServerHandshaker::new(self.attestation_behavior.clone())?,
            ))),
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
    pub fn put_session_state(&mut self, session_id: SessionId, session_state: SessionState<G, V>) {
        self.known_sessions.put(session_id, session_state);
    }
}
