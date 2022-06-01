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
use anyhow::bail;
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
    /// Configuration information to provide to the client for the attestation step.
    additional_info: Arc<Vec<u8>>,
    known_sessions: LruCache<SessionId, SessionState<G, V>>,
}

impl<G: AttestationGenerator, V: AttestationVerifier> SessionTracker<G, V> {
    pub fn create(
        cache_size: usize,
        attestation_behavior: AttestationBehavior<G, V>,
        additional_info: Vec<u8>,
    ) -> Self {
        let known_sessions = LruCache::new(cache_size);
        Self {
            attestation_behavior,
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
    ) -> anyhow::Result<SessionState<G, V>> {
        match self.known_sessions.pop(&session_id) {
            None => Ok(SessionState::HandshakeInProgress(Box::new(
                ServerHandshaker::new(
                    self.attestation_behavior.clone(),
                    self.additional_info.clone(),
                )?,
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

pub struct SerializeableRequest {
    pub session_id: SessionId,
    pub body: Vec<u8>,
}

impl From<SerializeableRequest> for Vec<u8> {
    fn from(serializeable_request: SerializeableRequest) -> Vec<u8> {
        // The payload is the request's body prepended with the 8 byte session_id.
        // This takes adavantage of the session_id's fixed size to avoid needing
        // to use a key/value pair binary serialization protocol.
        let mut serialized_request: Vec<u8> = Vec::with_capacity(
            serializeable_request.session_id.len() + serializeable_request.body.len(),
        );

        serialized_request.extend(serializeable_request.session_id);
        serialized_request.extend(serializeable_request.body);

        serialized_request
    }
}

impl TryFrom<&[u8]> for SerializeableRequest {
    type Error = anyhow::Error;

    fn try_from(serialized_request: &[u8]) -> Result<Self, Self::Error> {
        if serialized_request.len() < SESSION_ID_LENGTH {
            bail!(
                "Message too short to contain a SessionId. The length of a SessionId
                is {} bytes, the message received contained only {} bytes",
                SESSION_ID_LENGTH,
                serialized_request.len()
            );
        }

        let (session_id_slice, request_body_slice) = serialized_request.split_at(SESSION_ID_LENGTH);

        let mut session_id: SessionId = [0; SESSION_ID_LENGTH];
        session_id.copy_from_slice(session_id_slice);
        let body = request_body_slice.to_vec();

        Ok(Self { session_id, body })
    }
}
