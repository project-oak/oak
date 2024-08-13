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

use alloc::{boxed::Box, vec::Vec};
use core::convert::TryInto;

use aead::Error;
use anyhow::{anyhow, Context};
use oak_crypto::{
    identity_key::IdentityKeyHandle,
    noise_handshake::{client::HandshakeInitiator, respond_kk, respond_nk, respond_nn, Crypter},
};
use oak_proto_rust::oak::{
    crypto::v1::SessionKeys,
    session::v1::{
        handshake_request, handshake_response, HandshakeRequest, HandshakeResponse,
        NoiseHandshakeMessage,
    },
};

use crate::{config::HandshakerConfig, ProtocolEngine};

const P256_X962_KEY_BYTES_LEN: usize = 65;
const HANDSHAKE_HASH_LEN: usize = 32;

#[derive(Copy, Clone)]
pub enum HandshakeType {
    NoiseKK,
    NoiseKN,
    NoiseNK,
    NoiseNN,
}

pub trait Handshaker {
    fn derive_session_keys(&mut self) -> Option<SessionKeys>;
}

/// Client-side Handshaker that initiates the crypto handshake with the server.
#[allow(dead_code)]
pub struct ClientHandshaker {
    handshake_type: HandshakeType,
    handshake_initiator: HandshakeInitiator,
    handshake_result: Option<([u8; HANDSHAKE_HASH_LEN], Crypter)>,
}

impl ClientHandshaker {
    pub fn create(handshaker_config: HandshakerConfig) -> anyhow::Result<Self> {
        let handshake_type = handshaker_config.handshake_type;
        let peer_static_public_key = handshaker_config.peer_static_public_key.clone();
        Ok(Self {
            handshake_type,
            handshake_initiator: match handshake_type {
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
            },
            handshake_result: None,
        })
    }
}

impl Handshaker for ClientHandshaker {
    fn derive_session_keys(&mut self) -> Option<SessionKeys> {
        self.handshake_result.take().map(|(_handshake_hash, crypter)| crypter.into())
    }
}

impl ProtocolEngine<HandshakeResponse, HandshakeRequest> for ClientHandshaker {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<HandshakeRequest>> {
        let mut initial_message = self
            .handshake_initiator
            .build_initial_message()
            .map_err(|e| anyhow!("Error building initial message: {e:?}"))?;
        let (ciphertext, ephemeral_public_key) =
            (initial_message.split_off(P256_X962_KEY_BYTES_LEN), initial_message);
        Ok(Some(HandshakeRequest {
            r#handshake_type: Some(handshake_request::HandshakeType::NoiseHandshakeMessage(
                NoiseHandshakeMessage {
                    ephemeral_public_key,
                    static_public_key: match self.handshake_type {
                        HandshakeType::NoiseKK
                        | HandshakeType::NoiseKN
                        | HandshakeType::NoiseNK
                        | HandshakeType::NoiseNN => vec![],
                    },
                    ciphertext,
                },
            )),
            attestation_binding: None,
        }))
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &HandshakeResponse,
    ) -> anyhow::Result<Option<()>> {
        match incoming_message.r#handshake_type.as_ref() {
            Some(handshake_response::HandshakeType::NoiseHandshakeMessage(noise_message)) => {
                let handshake_response = [
                    noise_message.ephemeral_public_key.as_slice(),
                    noise_message.static_public_key.as_slice(),
                    noise_message.ciphertext.as_slice(),
                ]
                .concat();
                self.handshake_result = Some(
                    self.handshake_initiator
                        .process_response(handshake_response.as_slice())
                        .map_err(|e| anyhow!("Error processing response: {e:?}"))?,
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
    handshake_result: Option<SessionKeys>,
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
    fn derive_session_keys(&mut self) -> Option<SessionKeys> {
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
                let in_data = [
                    noise_message.ephemeral_public_key.as_slice(),
                    noise_message.static_public_key.as_slice(),
                    noise_message.ciphertext.as_slice(),
                ]
                .concat();
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
                        &in_data,
                    )
                    .map_err(|e| anyhow!("handshake response failed: {e:?}"))?,
                    HandshakeType::NoiseNK => respond_nk(
                        self.self_identity_key
                            .as_ref()
                            .context("handshaker_config missing the self private key")?
                            .as_ref(),
                        &in_data,
                    )
                    .map_err(|e| anyhow!("handshake response failed: {e:?}"))?,

                    HandshakeType::NoiseNN => respond_nn(&in_data)
                        .map_err(|e| anyhow!("handshake response failed: {e:?}"))?,
                }
            }
            None => return Err(anyhow!("Missing handshake_type")),
        };
        self.handshake_result = Some(noise_response.crypter.into());
        let mut response_message = noise_response.response.clone();
        let (ciphertext, ephemeral_public_key) =
            (response_message.split_off(P256_X962_KEY_BYTES_LEN), response_message);
        self.handshake_response = Some(HandshakeResponse {
            r#handshake_type: Some(handshake_response::HandshakeType::NoiseHandshakeMessage(
                NoiseHandshakeMessage {
                    ephemeral_public_key,
                    static_public_key: match self.handshake_type {
                        HandshakeType::NoiseKK
                        | HandshakeType::NoiseKN
                        | HandshakeType::NoiseNK
                        | HandshakeType::NoiseNN => vec![],
                    },
                    ciphertext,
                },
            )),
            attestation_binding: None,
        });
        Ok(Some(()))
    }
}
