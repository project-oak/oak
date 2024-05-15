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
//

//! This module provides an implementation of the Handshaker, which
//! handles cryptographic handshake and secure session creation.

use alloc::vec::Vec;

use oak_proto_rust::oak::{
    crypto::v1::SessionKeys,
    session::v1::{HandshakeRequest, HandshakeResponse},
};

pub trait EncryptionKeyHandle {
    fn derive_session_keys(
        &self,
        static_peer_public_key: &[u8],
        ephemeral_peer_public_key: &[u8],
    ) -> anyhow::Result<SessionKeys>;
}

pub enum HandshakeType {
    NoiseKK,
    NoiseNK,
}

/// Client-side Handshaker that initiates the crypto handshake with the server.
#[allow(dead_code)]
pub struct ClientHandshaker<'a> {
    handshake_type: HandshakeType,
    self_static_private_key: Option<&'a dyn EncryptionKeyHandle>,
    peer_static_public_key: Option<Vec<u8>>,
}

impl<'a> ClientHandshaker<'a> {
    pub fn new(
        handshake_type: HandshakeType,
        self_static_private_key: Option<&'a dyn EncryptionKeyHandle>,
        peer_static_public_key: Option<&[u8]>,
    ) -> Self {
        Self {
            handshake_type,
            self_static_private_key,
            peer_static_public_key: peer_static_public_key.map(|k| k.to_vec()),
        }
    }

    pub fn get_request(&mut self) -> anyhow::Result<HandshakeRequest> {
        core::unimplemented!();
    }

    pub fn put_response(&mut self, _response: HandshakeResponse) -> anyhow::Result<()> {
        core::unimplemented!();
    }

    pub fn derive_session_keys(self) -> Option<SessionKeys> {
        core::unimplemented!();
    }
}

/// Server-side Attestation Provider that responds to the crypto handshake
/// request from the client.
#[allow(dead_code)]
pub struct ServerHandshaker<'a> {
    handshake_type: HandshakeType,
    self_static_private_key: Option<&'a dyn EncryptionKeyHandle>,
    peer_static_public_key: Option<Vec<u8>>,
}

impl<'a> ServerHandshaker<'a> {
    pub fn new(
        handshake_type: HandshakeType,
        self_static_private_key: Option<&'a dyn EncryptionKeyHandle>,
        peer_static_public_key: Option<&[u8]>,
    ) -> Self {
        Self {
            handshake_type,
            self_static_private_key,
            peer_static_public_key: peer_static_public_key.map(|k| k.to_vec()),
        }
    }

    pub fn put_request(&mut self, _request: HandshakeRequest) -> anyhow::Result<()> {
        core::unimplemented!();
    }

    pub fn get_response(&mut self) -> anyhow::Result<HandshakeResponse> {
        core::unimplemented!();
    }

    pub fn derive_session_keys(self) -> Option<SessionKeys> {
        core::unimplemented!();
    }
}
