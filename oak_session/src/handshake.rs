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

use alloc::{boxed::Box, collections::BTreeMap, string::String, sync::Arc, vec::Vec};
use core::convert::TryInto;

use anyhow::{anyhow, Context, Error};
use oak_crypto::{
    identity_key::IdentityKeyHandle,
    noise_handshake::{client::HandshakeInitiator, respond_kk, respond_nk, respond_nn, Response},
};
use oak_proto_rust::oak::{
    crypto::v1::SessionKeys,
    session::v1::{
        handshake_request, handshake_response, HandshakeRequest, HandshakeResponse,
        NoiseHandshakeMessage, SessionBinding,
    },
};

use crate::{config::HandshakerConfig, session_binding::SessionBinder, ProtocolEngine};

#[derive(Copy, Clone, Debug)]
pub enum HandshakeType {
    NoiseKK,
    NoiseKN,
    NoiseNK,
    NoiseNN,
}

/// Struct that represents the data extracted from a successfully executed Noise
/// handshake.
pub struct HandshakeResult {
    /// The hash of the data exchanged in the handshake.
    pub handshake_hash: Vec<u8>,
    /// Bindings for the session, computed from the handshake hash by the other
    /// party.
    pub session_bindings: BTreeMap<String, SessionBinding>,
}

/// Trait that allows building a handshaker without passing any more data to it.
/// It encapsulates any parameters necessary to create a handshaker object
/// (i.e., the configuration)
pub trait HandshakerBuilder<T: Handshaker>: Send {
    fn build(self: Box<Self>) -> Result<T, Error>;
}

pub struct ClientHandshakerBuilder {
    pub config: HandshakerConfig,
}

impl HandshakerBuilder<ClientHandshaker> for ClientHandshakerBuilder {
    fn build(self: Box<Self>) -> Result<ClientHandshaker, Error> {
        ClientHandshaker::create(self.config)
    }
}
pub struct ServerHandshakerBuilder {
    pub config: HandshakerConfig,
    pub client_binding_expected: bool,
}

impl HandshakerBuilder<ServerHandshaker> for ServerHandshakerBuilder {
    fn build(self: Box<Self>) -> Result<ServerHandshaker, Error> {
        Ok(ServerHandshaker::new(self.config, self.client_binding_expected))
    }
}

/// Trait that performs a Noise handshake between the parties following the
/// pattern specified in the configuration.
pub trait Handshaker: Send {
    /// Consume the session keys produced by the handshake. Returns error if the
    /// keys are not ready. Can only be called once.
    fn take_session_keys(&mut self) -> Result<SessionKeys, Error>;

    /// Gets the result of the completed handshake. Returns error if the
    /// handshake is not complete. Can only be called once.
    fn take_handshake_result(&mut self) -> Result<HandshakeResult, Error>;

    // Allows checking whether the handshake is complete without consuming the
    // produced results.
    fn is_handshake_complete(&self) -> bool;
}

/// Client-side Handshaker that initiates the crypto handshake with the server.
pub struct ClientHandshaker {
    handshake_initiator: HandshakeInitiator,
    session_binders: BTreeMap<String, Arc<dyn SessionBinder>>,
    initial_message: Option<HandshakeRequest>,
    followup_message: Option<HandshakeRequest>,
    handshake_result: Option<HandshakeResult>,
    session_keys: Option<SessionKeys>,
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
        let initial_noise_message = handshake_initiator
            .build_initial_message()
            .map_err(|e| anyhow!("Error building initial message: {e:?}"))?;
        let initial_message = HandshakeRequest {
            r#handshake_type: Some(handshake_request::HandshakeType::NoiseHandshakeMessage(
                NoiseHandshakeMessage {
                    ephemeral_public_key: initial_noise_message.ephemeral_public_key,
                    static_public_key: match handshake_type {
                        HandshakeType::NoiseKK
                        | HandshakeType::NoiseKN
                        | HandshakeType::NoiseNK
                        | HandshakeType::NoiseNN => vec![],
                    },
                    ciphertext: initial_noise_message.ciphertext,
                },
            )),
            attestation_bindings: BTreeMap::new(),
        };
        Ok(Self {
            handshake_initiator,
            session_binders: handshaker_config.session_binders,
            initial_message: Some(initial_message),
            followup_message: None,
            handshake_result: None,
            session_keys: None,
        })
    }
}

impl Handshaker for ClientHandshaker {
    fn take_session_keys(&mut self) -> Result<SessionKeys, Error> {
        self.session_keys.take().ok_or(anyhow!("handshake is not complete"))
    }

    fn take_handshake_result(&mut self) -> Result<HandshakeResult, Error> {
        self.handshake_result.take().ok_or(anyhow!("handshake is not complete"))
    }

    fn is_handshake_complete(&self) -> bool {
        self.session_keys.is_some() && self.followup_message.is_none()
    }
}

impl ProtocolEngine<HandshakeResponse, HandshakeRequest> for ClientHandshaker {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<HandshakeRequest>> {
        if let Some(initial_message) = self.initial_message.take() {
            Ok(Some(initial_message))
        } else {
            Ok(self.followup_message.take())
        }
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: HandshakeResponse,
    ) -> anyhow::Result<Option<()>> {
        if self.session_keys.is_some() {
            // The session keys are ready - no other messages expected.
            return Ok(None);
        }
        match incoming_message.r#handshake_type {
            Some(handshake_response::HandshakeType::NoiseHandshakeMessage(noise_message)) => {
                let (handshake_hash, session_keys) = self
                    .handshake_initiator
                    .process_response(&noise_message.into())
                    .map_err(|e| anyhow!("Error processing response: {e:?}"))?;
                let session_keys = session_keys.into();
                let handshake_result = HandshakeResult {
                    handshake_hash: handshake_hash.to_vec(),
                    session_bindings: incoming_message.attestation_bindings,
                };
                if !self.session_binders.is_empty() {
                    self.followup_message = Some(HandshakeRequest {
                        r#handshake_type: None,
                        attestation_bindings: self
                            .session_binders
                            .iter()
                            .map(|(id, binder)| {
                                Ok((
                                    id.clone(),
                                    SessionBinding {
                                        binding: binder
                                            .bind(handshake_result.handshake_hash.as_slice()),
                                    },
                                ))
                            })
                            .collect::<Result<BTreeMap<String, SessionBinding>, Error>>()?,
                    });
                }
                self.handshake_result = Some(handshake_result);
                self.session_keys = Some(session_keys);
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
    session_binders: BTreeMap<String, Arc<dyn SessionBinder>>,
    client_binding_expected: bool,
    noise_response: Option<Response>,
    handshake_response: Option<HandshakeResponse>,
    handshake_result: Option<HandshakeResult>,
    session_keys: Option<SessionKeys>,
}

impl ServerHandshaker {
    pub fn new(handshaker_config: HandshakerConfig, client_binding_expected: bool) -> Self {
        Self {
            handshake_type: handshaker_config.handshake_type,
            self_identity_key: handshaker_config.self_static_private_key,
            peer_public_key: handshaker_config.peer_static_public_key,
            session_binders: handshaker_config.session_binders,
            client_binding_expected,
            noise_response: None,
            handshake_response: None,
            handshake_result: None,
            session_keys: None,
        }
    }
}

impl Handshaker for ServerHandshaker {
    fn take_session_keys(&mut self) -> Result<SessionKeys, Error> {
        self.session_keys.take().ok_or(anyhow!("handshake is not complete"))
    }

    fn take_handshake_result(&mut self) -> Result<HandshakeResult, Error> {
        self.handshake_result.take().ok_or(anyhow!("handshake is not complete"))
    }

    fn is_handshake_complete(&self) -> bool {
        self.session_keys.is_some()
    }
}

impl ProtocolEngine<HandshakeRequest, HandshakeResponse> for ServerHandshaker {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<HandshakeResponse>> {
        Ok(self.handshake_response.take())
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: HandshakeRequest,
    ) -> anyhow::Result<Option<()>> {
        if self.session_keys.is_some() {
            // The handshake result is ready - no other messages expected.
            return Ok(None);
        }
        if let Some(noise_response) = self.noise_response.take() {
            self.session_keys = Some(noise_response.crypter.into());
            self.handshake_result = Some(HandshakeResult {
                handshake_hash: noise_response.handshake_hash.to_vec(),
                session_bindings: incoming_message.attestation_bindings,
            });
        } else {
            let noise_response = match incoming_message.r#handshake_type {
                Some(handshake_request::HandshakeType::NoiseHandshakeMessage(noise_message)) => {
                    match self.handshake_type {
                        HandshakeType::NoiseKN => core::unimplemented!(),
                        HandshakeType::NoiseKK => respond_kk(
                            self.self_identity_key
                                .as_ref()
                                .context("handshaker_config missing the self private key")?
                                .as_ref(),
                            self.peer_public_key
                                .as_ref()
                                .ok_or(anyhow!("Must provide public key for Kk"))?,
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
            self.handshake_response = Some(HandshakeResponse {
                r#handshake_type: Some(handshake_response::HandshakeType::NoiseHandshakeMessage(
                    NoiseHandshakeMessage {
                        ephemeral_public_key: noise_response.response.ephemeral_public_key.clone(),
                        static_public_key: match self.handshake_type {
                            HandshakeType::NoiseKK
                            | HandshakeType::NoiseKN
                            | HandshakeType::NoiseNK
                            | HandshakeType::NoiseNN => vec![],
                        },
                        ciphertext: noise_response.response.ciphertext.clone(),
                    },
                )),
                attestation_bindings: self
                    .session_binders
                    .iter()
                    .map(|(id, binder)| {
                        Ok((
                            id.clone(),
                            SessionBinding {
                                binding: binder.bind(noise_response.handshake_hash.as_slice()),
                            },
                        ))
                    })
                    .collect::<Result<BTreeMap<String, SessionBinding>, Error>>()?,
            });
            if self.client_binding_expected {
                self.noise_response = Some(noise_response);
            } else {
                self.session_keys = Some(noise_response.crypter.into());
                self.handshake_result = Some(HandshakeResult {
                    handshake_hash: noise_response.handshake_hash.to_vec(),
                    session_bindings: BTreeMap::new(),
                })
            }
        }
        Ok(Some(()))
    }
}
