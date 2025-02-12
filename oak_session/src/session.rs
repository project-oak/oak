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

//! This module provides an SDK for creating secure attested sessions between
//! two parties.

use alloc::{
    boxed::Box,
    collections::{BTreeMap, VecDeque},
    string::String,
    sync::Arc,
};
use core::mem;

use anyhow::{anyhow, Context, Error, Ok};
use oak_crypto::encryptor::Encryptor;
use oak_proto_rust::oak::session::v1::{
    session_request::Request, session_response::Response, EncryptedMessage, PlaintextMessage,
    SessionBinding, SessionRequest, SessionResponse,
};

use crate::{
    attestation::{
        AttestationProvider, AttestationSuccess, AttestationType, ClientAttestationProvider,
        ServerAttestationProvider,
    },
    config::{EncryptorProvider, SessionConfig},
    handshake::{
        ClientHandshaker, ClientHandshakerBuilder, Handshaker, HandshakerBuilder, ServerHandshaker,
        ServerHandshakerBuilder,
    },
    key_extractor::KeyExtractor,
    session_binding::{SessionBindingVerifier, SignatureBindingVerifierBuilder},
    ProtocolEngine,
};

/// Trait that represents an end-to-end encrypted bidirectional streaming
/// session between two peers.
///
/// If one of the methods returns an error, it means that there was a protocol
/// error and the session needs to be restarted (because the state-machine is in
/// an incorrect state).
pub trait Session: Send {
    /// Checks whether session is ready to send and receive encrypted messages.
    /// Session becomes ready once remote attestation and crypto handshake have
    /// been successfully finished.
    fn is_open(&self) -> bool;

    /// Encrypts `plaintext` and send it to the peer.
    ///
    /// This function can be called multiple times in a row, which will result
    /// in multiple outgoing protocol messages being created.
    fn write(&mut self, plaintext: &PlaintextMessage) -> Result<(), Error>;

    /// Reads an encrypted message from the peer and decrypt it.
    ///
    /// This function can be called multiple times in a row, if the peer sent
    /// multiple protocol messages that need to be decrypted.
    ///
    /// Method returns `Result<Option<()>>` with the corresponding outcomes:
    /// - `Ok(None)`: Nothing to read
    /// - `Ok(Some(Vec<u8>))`: Successfully read plaintext bytes
    /// - `Err`: Protocol error
    fn read(&mut self) -> Result<Option<PlaintextMessage>, Error>;
}

/// Represents all data that is used for a particular session protocol step and
/// for transition to the next one. It is parametrized by the type of
/// attestation provider and handshaker (either the client or server version).
enum Step<AP: AttestationProvider, H: Handshaker> {
    /// Protocol step where communicating parties exchange and verify the
    /// attested evidence. May be skipped if no attestation is required.
    Attestation {
        attester: AP,
        handshaker_provider: Box<dyn HandshakerBuilder<H>>,
        encryptor_provider: Box<dyn EncryptorProvider>,
    },
    /// Protocol step for performing the Noise handshake.
    Handshake { handshaker: H, encryptor_provider: Box<dyn EncryptorProvider> },
    /// Session is open and allows encrypted communication.
    Open(Box<dyn Encryptor>),
    /// Invalid state. The session is only temporarily put into this state if
    /// the transition between steps cannot be performed atomically.
    Invalid,
}

impl<AP: AttestationProvider, H: Handshaker> Step<AP, H> {
    fn next(&mut self) -> Result<(), Error> {
        // We can't transition between states without using this temp variable while
        // ensuring the memory safety because of the objects' lifetime.
        let old_state = mem::replace(self, Step::Invalid);
        match old_state {
            Step::Attestation { attester: _, handshaker_provider, encryptor_provider } => {
                *self = Step::Handshake {
                    encryptor_provider,
                    handshaker: handshaker_provider.build()?,
                };
            }
            Step::Handshake { handshaker, encryptor_provider } => {
                *self = Step::Open(
                    encryptor_provider.provide_encryptor(handshaker.take_session_keys()?)?,
                );
            }
            Step::Open(_) => return Err(anyhow!("there is no next step when the session is open")),
            Step::Invalid => return Err(anyhow!("session is currently in an invalid state")),
        };
        Ok(())
    }
}

/// Client-side secure attested session entrypoint.
pub struct ClientSession {
    step: Step<ClientAttestationProvider, ClientHandshaker>,
    binding_key_extractors: BTreeMap<String, Arc<dyn KeyExtractor>>,
    attestation_result: Option<AttestationSuccess>,
    outgoing_requests: VecDeque<SessionRequest>,
    incoming_responses: VecDeque<SessionResponse>,
}

impl ClientSession {
    pub fn create(config: SessionConfig) -> Result<Self, Error> {
        Ok(Self {
            step: match config.attestation_provider_config.attestation_type {
                AttestationType::Bidirectional
                | AttestationType::SelfUnidirectional
                | AttestationType::PeerUnidirectional => Step::Attestation {
                    attester: ClientAttestationProvider::create(
                        config.attestation_provider_config,
                    )?,
                    handshaker_provider: Box::new(ClientHandshakerBuilder {
                        config: config.handshaker_config,
                    }),
                    encryptor_provider: config.encryptor_config.encryptor_provider,
                },
                AttestationType::Unattested => Step::Handshake {
                    handshaker: ClientHandshaker::create(config.handshaker_config)?,
                    encryptor_provider: config.encryptor_config.encryptor_provider,
                },
            },
            binding_key_extractors: config.binding_key_extractors,
            attestation_result: None,
            outgoing_requests: VecDeque::new(),
            incoming_responses: VecDeque::new(),
        })
    }
}

impl Session for ClientSession {
    fn is_open(&self) -> bool {
        matches!(self.step, Step::Open(_))
    }

    fn write(&mut self, plaintext: &PlaintextMessage) -> Result<(), Error> {
        match &mut self.step {
            Step::Attestation { .. } | Step::Handshake { .. } | Step::Invalid => {
                Err(anyhow!("the session is not open"))
            }
            Step::Open(encryptor) => {
                let encrypted_message: EncryptedMessage = encryptor
                    .encrypt(&plaintext.clone().into())
                    .map(From::from)
                    .context("couldn't encrypt the supplied plaintext")?;
                self.outgoing_requests.push_back(SessionRequest {
                    request: Some(Request::EncryptedMessage(encrypted_message)),
                });
                Ok(())
            }
        }
    }

    fn read(&mut self) -> Result<Option<PlaintextMessage>, Error> {
        match &mut self.step {
            Step::Attestation { .. } | Step::Handshake { .. } | Step::Invalid => {
                Err(anyhow!("the session is not open"))
            }
            Step::Open(encryptor) => match self.incoming_responses.pop_front() {
                Some(response) => {
                    let encrypted_message = match response.response {
                        Some(Response::EncryptedMessage(encrypted_message)) => encrypted_message,
                        _ => {
                            return Err(anyhow!(
                                "unexpected content of SessionResponse: no encrypted message set"
                            ));
                        }
                    };
                    Ok(Some(
                        encryptor
                            .decrypt(&encrypted_message.into())
                            .map(From::from)
                            .context("couldn't decrypt the supplied plaintext")?,
                    ))
                }
                None => Ok(None),
            },
        }
    }
}

impl ProtocolEngine<SessionResponse, SessionRequest> for ClientSession {
    fn get_outgoing_message(&mut self) -> Result<Option<SessionRequest>, Error> {
        match &mut self.step {
            Step::Attestation { attester, .. } => {
                if let Some(attest_message) = attester.get_outgoing_message()? {
                    return Ok(Some(SessionRequest {
                        request: Some(Request::AttestRequest(attest_message)),
                    }));
                } else {
                    return Err(anyhow!(
                        "attestation not yet complete but there are no outgoing messages"
                    ));
                }
            }
            Step::Handshake { handshaker, .. } => {
                if let Some(handshake_message) = handshaker.get_outgoing_message()? {
                    if handshaker.is_handshake_complete() {
                        self.step.next()?;
                    }
                    return Ok(Some(SessionRequest {
                        request: Some(Request::HandshakeRequest(handshake_message)),
                    }));
                }
            }
            Step::Open(_) => {}
            Step::Invalid => return Err(anyhow!("session is in an invalid state")),
        }

        Ok(self.outgoing_requests.pop_front())
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &SessionResponse,
    ) -> Result<Option<()>, Error> {
        match (incoming_message.response.as_ref(), &mut self.step) {
            (
                Some(Response::AttestResponse(attest_message)),
                Step::Attestation { attester, .. },
            ) => {
                attester.put_incoming_message(attest_message)?.ok_or(anyhow!(
                    "invalid session state: attest message received but attester doesn't expect
                     any"
                ))?;
                if let Some(attestation_result) = attester.take_attestation_result() {
                    self.attestation_result = Some(attestation_result?);
                    self.step.next()?;
                }
                Ok(Some(()))
            }
            (
                Some(Response::HandshakeResponse(handshake_message)),
                Step::Handshake { handshaker, .. },
            ) => {
                handshaker.put_incoming_message(handshake_message)?.ok_or(anyhow!(
                    "invalid session state: handshake message received but handshaker doesn't
                     expect any"
                ))?;
                if let Some(attestation_result) = &self.attestation_result {
                    verify_session_binding(
                        &self.binding_key_extractors,
                        attestation_result,
                        &handshake_message.attestation_bindings,
                        handshaker.get_handshake_hash()?.as_slice(),
                    )?;
                }
                if handshaker.is_handshake_complete() {
                    self.step.next()?;
                }
                Ok(Some(()))
            }
            (Some(Response::EncryptedMessage(_)), Step::Open(_)) => {
                self.incoming_responses.push_back(incoming_message.clone());
                Ok(Some(()))
            }
            (_, _) => Err(anyhow!("unexpected content of session response")),
        }
    }
}

// Server-side secure attested session entrypoint.
pub struct ServerSession {
    step: Step<ServerAttestationProvider, ServerHandshaker>,
    binding_key_extractors: BTreeMap<String, Arc<dyn KeyExtractor>>,
    // encryptor is initialized once the handshake is completed and the session becomes open
    attestation_result: Option<AttestationSuccess>,
    outgoing_responses: VecDeque<SessionResponse>,
    incoming_requests: VecDeque<SessionRequest>,
}

impl ServerSession {
    pub fn create(config: SessionConfig) -> Result<Self, Error> {
        let client_binding_expected = matches!(
            config.attestation_provider_config.attestation_type,
            AttestationType::Bidirectional | AttestationType::PeerUnidirectional
        );
        Ok(Self {
            step: match config.attestation_provider_config.attestation_type {
                AttestationType::Bidirectional
                | AttestationType::SelfUnidirectional
                | AttestationType::PeerUnidirectional => Step::Attestation {
                    attester: ServerAttestationProvider::create(
                        config.attestation_provider_config,
                    )?,
                    handshaker_provider: Box::new(ServerHandshakerBuilder {
                        config: config.handshaker_config,
                        client_binding_expected,
                    }),
                    encryptor_provider: config.encryptor_config.encryptor_provider,
                },
                AttestationType::Unattested => Step::Handshake {
                    handshaker: ServerHandshaker::new(
                        config.handshaker_config,
                        client_binding_expected,
                    ),
                    encryptor_provider: config.encryptor_config.encryptor_provider,
                },
            },
            binding_key_extractors: config.binding_key_extractors,
            attestation_result: None,
            outgoing_responses: VecDeque::new(),
            incoming_requests: VecDeque::new(),
        })
    }
}

impl Session for ServerSession {
    fn is_open(&self) -> bool {
        matches!(self.step, Step::Open(_))
    }

    fn write(&mut self, plaintext: &PlaintextMessage) -> Result<(), Error> {
        match &mut self.step {
            Step::Attestation { .. } | Step::Handshake { .. } | Step::Invalid => {
                Err(anyhow!("the session is not open"))
            }
            Step::Open(encryptor) => {
                let encrypted_message: EncryptedMessage = encryptor
                    .encrypt(&plaintext.clone().into())
                    .map(From::from)
                    .context("couldn't encrypt the supplied plaintext")?;
                self.outgoing_responses.push_back(SessionResponse {
                    response: Some(Response::EncryptedMessage(encrypted_message)),
                });
                Ok(())
            }
        }
    }

    fn read(&mut self) -> Result<Option<PlaintextMessage>, Error> {
        match &mut self.step {
            Step::Attestation { .. } | Step::Handshake { .. } | Step::Invalid => {
                Err(anyhow!("the session is not open"))
            }
            Step::Open(encryptor) => match self.incoming_requests.pop_front() {
                Some(request) => {
                    let encrypted_message = match request.request {
                        Some(Request::EncryptedMessage(encrypted_message)) => encrypted_message,
                        _ => {
                            return Err(anyhow!(
                                "unexpected content of SessionRequest: no encrypted message set"
                            ));
                        }
                    };
                    Ok(Some(
                        encryptor
                            .decrypt(&encrypted_message.into())
                            .map(From::from)
                            .context("couldn't decrypt the supplied plaintext")?,
                    ))
                }
                None => Ok(None),
            },
        }
    }
}

impl ProtocolEngine<SessionRequest, SessionResponse> for ServerSession {
    fn get_outgoing_message(&mut self) -> Result<Option<SessionResponse>, Error> {
        match &mut self.step {
            Step::Attestation { attester, .. } => {
                if let Some(attest_message) = attester.get_outgoing_message()? {
                    if let Some(attestation_result) = attester.take_attestation_result() {
                        self.attestation_result = Some(attestation_result?);
                        self.step.next()?;
                    }
                    Ok(Some(SessionResponse {
                        response: Some(Response::AttestResponse(attest_message)),
                    }))
                } else {
                    Err(anyhow!("attestation not yet completed but there are no outgoing messages"))
                }
            }
            Step::Handshake { handshaker, .. } => {
                let response = handshaker.get_outgoing_message()?;
                if handshaker.is_handshake_complete() {
                    self.step.next()?;
                }
                if let Some(handshake_message) = response {
                    Ok(Some(SessionResponse {
                        response: Some(Response::HandshakeResponse(handshake_message)),
                    }))
                } else {
                    Ok(None)
                }
            }
            Step::Open(_) => Ok(self.outgoing_responses.pop_front()),
            Step::Invalid => Err(anyhow!("session is in an invalid state")),
        }
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &SessionRequest,
    ) -> Result<Option<()>, Error> {
        match (incoming_message.request.as_ref(), &mut self.step) {
            (Some(Request::AttestRequest(attest_message)), Step::Attestation { attester, .. }) => {
                attester.put_incoming_message(attest_message)?.ok_or(anyhow!(
                    "invalid session state: attest message received but attester doesn't expect
                     any"
                ))?;
                Ok(Some(()))
            }
            (
                Some(Request::HandshakeRequest(handshake_message)),
                Step::Handshake { handshaker, .. },
            ) => {
                handshaker.put_incoming_message(handshake_message)?.ok_or(anyhow!(
                    "invalid session state: handshake message received but handshaker doesn't
                     expect any"
                ))?;
                if handshaker.is_handshake_complete() {
                    if let Some(attestation_result) = &self.attestation_result {
                        verify_session_binding(
                            &self.binding_key_extractors,
                            attestation_result,
                            &handshake_message.attestation_bindings,
                            handshaker.get_handshake_hash()?.as_slice(),
                        )?;
                    }
                }
                Ok(Some(()))
            }
            (Some(Request::EncryptedMessage(_)), Step::Open(_)) => {
                self.incoming_requests.push_back(incoming_message.clone());
                Ok(Some(()))
            }
            (_, _) => Err(anyhow!("unexpected content of session response")),
        }
    }
}

fn verify_session_binding(
    binding_key_extractors: &BTreeMap<String, Arc<dyn KeyExtractor>>,
    attestation: &AttestationSuccess,
    bindings: &BTreeMap<String, SessionBinding>,
    handshake_hash: &[u8],
) -> Result<(), Error> {
    for (verifier_id, results) in &attestation.attestation_results {
        let binding_key_extractor = binding_key_extractors
            .get(verifier_id)
            .ok_or(anyhow!("no key provider supplied for the verifier ID {verifier_id}"))?;
        let binding_verifier = SignatureBindingVerifierBuilder::default()
            .verifier(binding_key_extractor.extract_verifying_key(results)?)
            .build()
            .map_err(|err| anyhow!("couldn't build SignatureBindingVerifier: {}", err))?;
        binding_verifier.verify_binding(
            handshake_hash,
            bindings
                .get(verifier_id)
                .ok_or(anyhow!("handshake message doesn't have a binding for ID {}", verifier_id))?
                .binding
                .as_slice(),
        )?;
    }
    Ok(())
}
