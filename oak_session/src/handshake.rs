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

use oak_proto_rust::oak::{
    crypto::v1::SessionKeys,
    session::v1::{HandshakeRequest, HandshakeResponse},
};

use crate::{config::HandshakerConfig, ProtocolEngine};

pub trait EncryptionKeyHandle {
    fn derive_session_keys(
        &self,
        static_peer_public_key: &[u8],
        ephemeral_peer_public_key: &[u8],
    ) -> anyhow::Result<SessionKeys>;
}

pub enum HandshakeType {
    NoiseKK,
    NoiseKN,
    NoiseNK,
}

pub trait Handshaker {
    fn derive_session_keys(self) -> Option<SessionKeys>;
}

/// Client-side Handshaker that initiates the crypto handshake with the server.
#[allow(dead_code)]
pub struct ClientHandshaker<'a> {
    handshaker_config: HandshakerConfig<'a>,
}

impl<'a> ClientHandshaker<'a> {
    pub fn new(handshaker_config: HandshakerConfig<'a>) -> Self {
        Self { handshaker_config }
    }
}

impl<'a> Handshaker for ClientHandshaker<'a> {
    fn derive_session_keys(self) -> Option<SessionKeys> {
        core::unimplemented!();
    }
}

impl<'a> ProtocolEngine<HandshakeResponse, HandshakeRequest> for ClientHandshaker<'a> {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<HandshakeRequest>> {
        core::unimplemented!();
    }

    fn put_incoming_message(
        &mut self,
        _incoming_message: &HandshakeResponse,
    ) -> anyhow::Result<Option<()>> {
        core::unimplemented!();
    }
}

/// Server-side Handshaker that responds to the crypto handshake request from
/// the client.
#[allow(dead_code)]
pub struct ServerHandshaker<'a> {
    handshaker_config: HandshakerConfig<'a>,
}

impl<'a> ServerHandshaker<'a> {
    pub fn new(handshaker_config: HandshakerConfig<'a>) -> Self {
        Self { handshaker_config }
    }
}

impl<'a> Handshaker for ServerHandshaker<'a> {
    fn derive_session_keys(self) -> Option<SessionKeys> {
        core::unimplemented!();
    }
}

impl<'a> ProtocolEngine<HandshakeRequest, HandshakeResponse> for ServerHandshaker<'a> {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<HandshakeResponse>> {
        core::unimplemented!();
    }

    fn put_incoming_message(
        &mut self,
        _incoming_message: &HandshakeRequest,
    ) -> anyhow::Result<Option<()>> {
        core::unimplemented!();
    }
}
