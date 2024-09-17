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

use alloc::{boxed::Box, collections::BTreeMap, vec::Vec};
use core::convert::TryInto;

use aead::Error;
use anyhow::{anyhow, Context};
use oak_crypto::{
    identity_key::IdentityKeyHandle,
    noise_handshake::{
        client::HandshakeInitiator, respond_kk, respond_nk, respond_nn, NoiseMessage,
    },
};
use oak_proto_rust::oak::{
    crypto::v1::SessionKeys,
    session::v1::{
        handshake_request, handshake_response, HandshakeRequest, HandshakeResponse,
        NoiseHandshakeMessage,
    },
};

use crate::{config::HandshakerConfig, ProtocolEngine};

#[derive(Copy, Clone)]
pub enum HandshakeType {
    NoiseKK,
    NoiseKN,
    NoiseNK,
    NoiseNN,
}

pub struct HandshakeResult {
    pub session_keys: SessionKeys,
    pub handshake_hash: Vec<u8>,
}

pub trait Handshaker: Send {
    // Consume the handshake result when it's ready. Returns None if the handshake
    // is still in progress or its results have already been consumed.
    fn take_handshake_result(&mut self) -> Option<HandshakeResult>;
}

/// Client-side Handshaker that initiates the crypto handshake with the server.
pub struct ClientHandshaker {
    handshake_type: HandshakeType,
    handshake_initiator: HandshakeInitiator,
    initial_message: Option<NoiseMessage>,
    handshake_result: Option<HandshakeResult>,
}

impl ClientHandshaker {
    pub fn create(handshaker_config: HandshakerConfig) -> anyhow::Result<Self> {
        let handshake_type = handshaker_config.handshake_type;
        let peer_static_public_key = handshaker_config.peer_static_public_key.clone();
        let mut handshake_initiator = match handshake_type {
            HandshakeType::NoiseKN => core::unimplemented!(),
            HandshakeType::NoiseKK => HandshakeInitiator::new_kk(
                peer_static_public_key
                    .context("handshaker_config missing the peer public key")?
                    .as_slice()
                    .try_into()
                    .map_err(|error| anyhow!("invalid peer public key: {:?}", error))?,
                handshaker_config
                    .self_static_private_key
                    .context("handshaker_config missing the self static private key")?,
            ),
            HandshakeType::NoiseNK => HandshakeInitiator::new_nk(
                peer_static_public_key
                    .context("handshaker_config missing the peer public key")?
                    .as_slice()
                    .try_into()
                    .map_err(|error| anyhow!("invalid peer public key: {:?}", error))?,
            ),
            HandshakeType::NoiseNN => HandshakeInitiator::new_nn(),
        };
        let initial_message = handshake_initiator
            .build_initial_message()
            .map_err(|e| anyhow!("Error building initial message: {e:?}"))?;
        Ok(Self {
            handshake_type,
            handshake_initiator,
            initial_message: Some(initial_message),
            handshake_result: None,
        })
    }
}

impl Handshaker for ClientHandshaker {
    fn take_handshake_result(&mut self) -> Option<HandshakeResult> {
        self.handshake_result.take()
    }
}

impl ProtocolEngine<HandshakeResponse, HandshakeRequest> for ClientHandshaker {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<HandshakeRequest>> {
        Ok(self.initial_message.take().map(|initial_message| HandshakeRequest {
            r#handshake_type: Some(handshake_request::HandshakeType::NoiseHandshakeMessage(
                NoiseHandshakeMessage {
                    ephemeral_public_key: initial_message.ephemeral_public_key,
                    static_public_key: match self.handshake_type {
                        HandshakeType::NoiseKK
                        | HandshakeType::NoiseKN
                        | HandshakeType::NoiseNK
                        | HandshakeType::NoiseNN => vec![],
                    },
                    ciphertext: initial_message.ciphertext,
                },
            )),
            attestation_bindings: BTreeMap::new(),
        }))
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &HandshakeResponse,
    ) -> anyhow::Result<Option<()>> {
        match incoming_message.r#handshake_type.as_ref() {
            Some(handshake_response::HandshakeType::NoiseHandshakeMessage(noise_message)) => {
                self.handshake_result = Some(
                    self.handshake_initiator
                        .process_response(&noise_message.into())
                        .map_err(|e| anyhow!("Error processing response: {e:?}"))
                        .map(|(handshake_hash, crypter)| HandshakeResult {
                            session_keys: crypter.into(),
                            handshake_hash: handshake_hash.to_vec(),
                        })?,
                );
                Ok(Some(()))
            }
            None => Err(anyhow!("Missing handshake_type")),
        }
    }
}

/// Server-side Handshaker that responds to the crypto handshake request from
/// the client.
#[allow(dead_code)]
pub struct ServerHandshaker {
    handshake_type: HandshakeType,
    self_identity_key: Option<Box<dyn IdentityKeyHandle>>,
    peer_public_key: Option<Vec<u8>>,
    handshake_response: Option<HandshakeResponse>,
    handshake_result: Option<HandshakeResult>,
}

impl ServerHandshaker {
    pub fn new(handshaker_config: HandshakerConfig) -> Self {
        Self {
            handshake_type: handshaker_config.handshake_type,
            self_identity_key: handshaker_config.self_static_private_key,
            peer_public_key: handshaker_config.peer_static_public_key,
            handshake_response: None,
            handshake_result: None,
        }
    }
}

impl Handshaker for ServerHandshaker {
    fn take_handshake_result(&mut self) -> Option<HandshakeResult> {
        self.handshake_result.take()
    }
}

impl ProtocolEngine<HandshakeRequest, HandshakeResponse> for ServerHandshaker {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<HandshakeResponse>> {
        Ok(self.handshake_response.take())
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &HandshakeRequest,
    ) -> anyhow::Result<Option<()>> {
        let noise_response = match incoming_message.r#handshake_type.as_ref() {
            Some(handshake_request::HandshakeType::NoiseHandshakeMessage(noise_message)) => {
                match self.handshake_type {
                    HandshakeType::NoiseKN => core::unimplemented!(),
                    HandshakeType::NoiseKK => respond_kk(
                        self.self_identity_key
                            .as_ref()
                            .context("handshaker_config missing the self private key")?
                            .as_ref(),
                        &self
                            .peer_public_key
                            .as_ref()
                            .ok_or(|_: Error| "")
                            .map_err(|_| anyhow!("Must provide public key for Kk"))?,
                        &noise_message.into(),
                    )
                    .map_err(|e| anyhow!("handshake response failed: {e:?}"))?,
                    HandshakeType::NoiseNK => respond_nk(
                        self.self_identity_key
                            .as_ref()
                            .context("handshaker_config missing the self private key")?
                            .as_ref(),
                        &noise_message.into(),
                    )
                    .map_err(|e| anyhow!("handshake response failed: {e:?}"))?,
                    HandshakeType::NoiseNN => respond_nn(&noise_message.into())
                        .map_err(|e| anyhow!("handshake response failed: {e:?}"))?,
                }
            }
            None => return Err(anyhow!("Missing handshake_type")),
        };
        self.handshake_result = Some(HandshakeResult {
            session_keys: noise_response.crypter.into(),
            handshake_hash: noise_response.handshake_hash.to_vec(),
        });
        self.handshake_response = Some(HandshakeResponse {
            r#handshake_type: Some(handshake_response::HandshakeType::NoiseHandshakeMessage(
                NoiseHandshakeMessage {
                    ephemeral_public_key: noise_response.response.ephemeral_public_key,
                    static_public_key: match self.handshake_type {
                        HandshakeType::NoiseKK
                        | HandshakeType::NoiseKN
                        | HandshakeType::NoiseNK
                        | HandshakeType::NoiseNN => vec![],
                    },
                    ciphertext: noise_response.response.ciphertext,
                },
            )),
            attestation_bindings: BTreeMap::new(),
        });
        Ok(Some(()))
    }
}
