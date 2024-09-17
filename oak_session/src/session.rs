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
};

use anyhow::{anyhow, Context, Error, Ok};
use oak_crypto::encryptor::Encryptor;
use oak_proto_rust::oak::session::v1::{
    session_request::Request, session_response::Response, EncryptedMessage, PlaintextMessage,
    SessionBinding, SessionRequest, SessionResponse,
};
use prost::Message;

use crate::{
    attestation::{
        AttestationFailure, AttestationProvider, AttestationSuccess, ClientAttestationProvider,
        ServerAttestationProvider,
    },
    config::{EncryptorConfig, SessionConfig},
    handshake::{ClientHandshaker, Handshaker, ServerHandshaker},
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
    fn write(&mut self, plaintext: &PlaintextMessage) -> anyhow::Result<()>;

    /// Reads an encrypted message from the peer and decrypt it.
    ///
    /// This function can be called multiple times in a row, if the peer sent
    /// multiple protocol messages that need to be decrypted.
    ///
    /// Method returns `Result<Option<()>>` with the corresponding outcomes:
    /// - `Ok(None)`: Nothing to read
    /// - `Ok(Some(Vec<u8>))`: Successfully read plaintext bytes
    /// - `Err`: Protocol error
    fn read(&mut self) -> anyhow::Result<Option<PlaintextMessage>>;
}

// Client-side secure attested session entrypoint.
pub struct ClientSession {
    attester: ClientAttestationProvider,
    handshaker: ClientHandshaker,
    // encryptor is initialized once the handshake is completed and the session becomes open
    encryptor_config: EncryptorConfig,
    attestation_result: Option<Result<AttestationSuccess, AttestationFailure>>,
    encryptor: Option<Box<dyn Encryptor>>,
    outgoing_requests: VecDeque<SessionRequest>,
    incoming_responses: VecDeque<SessionResponse>,
}

impl ClientSession {
    pub fn create(config: SessionConfig) -> Result<Self, Error> {
        Ok(Self {
            attester: ClientAttestationProvider::new(config.attestation_provider_config),
            handshaker: ClientHandshaker::create(config.handshaker_config)
                .context("couldn't create the client handshaker")?,
            encryptor_config: config.encryptor_config,
            attestation_result: None,
            encryptor: None,
            outgoing_requests: VecDeque::new(),
            incoming_responses: VecDeque::new(),
        })
    }
}

impl Session for ClientSession {
    fn is_open(&self) -> bool {
        self.encryptor.is_some()
    }

    fn write(&mut self, plaintext: &PlaintextMessage) -> anyhow::Result<()> {
        if let Some(encryptor) = self.encryptor.as_mut() {
            let encrypted_message: EncryptedMessage = encryptor
                .encrypt(&plaintext.clone().into())
                .map(From::from)
                .context("couldn't encrypt the supplied plaintext")?;
            self.outgoing_requests.push_back(SessionRequest {
                request: Some(Request::EncryptedMessage(encrypted_message.into())),
            });
            Ok(())
        } else {
            Err(anyhow!("the session is not open"))
        }
    }

    fn read(&mut self) -> anyhow::Result<Option<PlaintextMessage>> {
        if let Some(encryptor) = self.encryptor.as_mut() {
            match self.incoming_responses.pop_front() {
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
            }
        } else {
            Err(anyhow!("the session is not open"))
        }
    }
}

impl ProtocolEngine<SessionResponse, SessionRequest> for ClientSession {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<SessionRequest>> {
        if let Some(attest_message) = self.attester.get_outgoing_message()? {
            return Ok(Some(SessionRequest {
                request: Some(Request::AttestRequest(attest_message)),
            }));
        }
        if let Some(handshake_message) = self.handshaker.get_outgoing_message()? {
            return Ok(Some(SessionRequest {
                request: Some(Request::HandshakeRequest(handshake_message)),
            }));
        }
        if self.is_open() {
            return Ok(self.outgoing_requests.pop_front());
        };
        Err(anyhow!("session in unexpected state"))
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &SessionResponse,
    ) -> anyhow::Result<Option<()>> {
        match incoming_message.response.as_ref() {
            Some(Response::AttestResponse(attest_message)) => {
                self.attester.put_incoming_message(&attest_message)?.ok_or(anyhow!(
                    "invalid session state: attest message received but attester doesn't expect
                     any"
                ))?;
                if let Some(attestation_result) = self.attester.take_attestation_result() {
                    self.attestation_result = Some(attestation_result);
                }
                Ok(Some(()))
            }
            Some(Response::HandshakeResponse(handshake_message)) => {
                self.handshaker.put_incoming_message(&handshake_message)?.ok_or(anyhow!(
                    "invalid session state: handshake message received but handshaker doesn't
                     expect any"
                ))?;
                if let Some(handshake_result) = self.handshaker.take_handshake_result() {
                    if let Some(attestation_result) = &self.attestation_result {
                        verify_session_binding(
                            &attestation_result,
                            &handshake_message.attestation_bindings,
                            handshake_result.handshake_hash.as_slice(),
                        )?;
                    }
                    self.encryptor = Some(
                        (self.encryptor_config.encryptor_provider)(handshake_result.session_keys)
                            .context("couldn't create an encryptor from the session key")?,
                    )
                }
                Ok(Some(()))
            }
            Some(Response::EncryptedMessage(_)) => {
                if self.is_open() {
                    self.incoming_responses.push_back(incoming_message.clone());
                    return Ok(Some(()));
                } else {
                    return Err(anyhow!(
                        "invalid session state: incoming encrypted message received but session is not open"
                    ));
                }
            }
            _ => Err(anyhow!("unexpected content of session response")),
        }
    }
}

// Server-side secure attested session entrypoint.
pub struct ServerSession {
    attester: ServerAttestationProvider,
    handshaker: ServerHandshaker,
    // encryptor is initialized once the handshake is completed and the session becomes open
    encryptor_config: EncryptorConfig,
    attestation_result: Option<Result<AttestationSuccess, AttestationFailure>>,
    encryptor: Option<Box<dyn Encryptor>>,
    outgoing_responses: VecDeque<SessionResponse>,
    incoming_requests: VecDeque<SessionRequest>,
}

impl ServerSession {
    pub fn new(config: SessionConfig) -> Self {
        Self {
            attester: ServerAttestationProvider::new(config.attestation_provider_config),
            handshaker: ServerHandshaker::new(config.handshaker_config),
            encryptor_config: config.encryptor_config,
            attestation_result: None,
            encryptor: None,
            outgoing_responses: VecDeque::new(),
            incoming_requests: VecDeque::new(),
        }
    }
}

impl Session for ServerSession {
    fn is_open(&self) -> bool {
        self.encryptor.is_some()
    }

    fn write(&mut self, plaintext: &PlaintextMessage) -> anyhow::Result<()> {
        if let Some(encryptor) = self.encryptor.as_mut() {
            let encrypted_message = encryptor
                .encrypt(&plaintext.clone().into())
                .map(From::from)
                .context("couldn't encrypt the supplied plaintext")?;
            self.outgoing_responses.push_back(SessionResponse {
                response: Some(Response::EncryptedMessage(encrypted_message)),
            });
            Ok(())
        } else {
            Err(anyhow!("the session is not open"))
        }
    }

    fn read(&mut self) -> anyhow::Result<Option<PlaintextMessage>> {
        if let Some(encryptor) = self.encryptor.as_mut() {
            match self.incoming_requests.pop_front() {
                Some(request) => {
                    let encrypted_message = match request.request {
                        Some(Request::EncryptedMessage(encrypted_message)) => encrypted_message,
                        _ => {
                            return Err(anyhow!(
                                "unexpected content of SessionRequest: no ciphertext set"
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
            }
        } else {
            Err(anyhow!("the session is not open"))
        }
    }
}

impl ProtocolEngine<SessionRequest, SessionResponse> for ServerSession {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<SessionResponse>> {
        if let Some(attest_message) = self.attester.get_outgoing_message()? {
            return Ok(Some(SessionResponse {
                response: Some(Response::AttestResponse(attest_message)),
            }));
        }
        if let Some(handshake_message) = self.handshaker.get_outgoing_message()? {
            return Ok(Some(SessionResponse {
                response: Some(Response::HandshakeResponse(handshake_message)),
            }));
        }
        if self.is_open() {
            return Ok(self.outgoing_responses.pop_front());
        };
        Err(anyhow!("session in unexpected state"))
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &SessionRequest,
    ) -> anyhow::Result<Option<()>> {
        match incoming_message.request.as_ref() {
            Some(Request::AttestRequest(attest_message)) => {
                self.attester.put_incoming_message(&attest_message)?.ok_or(anyhow!(
                    "invalid session state: attest message received but attester doesn't expect
                 any"
                ))?;
                if let Some(attestation_result) = self.attester.take_attestation_result() {
                    self.attestation_result = Some(attestation_result);
                }
                Ok(Some(()))
            }
            Some(Request::HandshakeRequest(handshake_message)) => {
                self.handshaker.put_incoming_message(&handshake_message)?.ok_or(anyhow!(
                    "invalid session state: handshake message received but handshaker doesn't
                 expect any"
                ))?;
                if let Some(handshake_result) = self.handshaker.take_handshake_result() {
                    if let Some(attestation_result) = &self.attestation_result {
                        verify_session_binding(
                            &attestation_result,
                            &handshake_message.attestation_bindings,
                            handshake_result.handshake_hash.as_slice(),
                        )?;
                    }
                    self.encryptor = Some(
                        (self.encryptor_config.encryptor_provider)(handshake_result.session_keys)
                            .context("couldn't create an encryptor from the session key")?,
                    )
                }
                Ok(Some(()))
            }
            Some(Request::EncryptedMessage(_)) => {
                if self.is_open() {
                    self.incoming_requests.push_back(incoming_message.clone());
                    return Ok(Some(()));
                } else {
                    return Err(anyhow!(
                        "invalid session state: incoming encrypted message received but session is not open"
                    ));
                }
            }
            _ => Err(anyhow!("unexpected content of session response")),
        }
    }
}

fn verify_session_binding(
    attestation_result: &Result<AttestationSuccess, AttestationFailure>,
    bindings: &BTreeMap<String, SessionBinding>,
    handshake_hash: &[u8],
) -> Result<(), Error> {
    let attestation = attestation_result
        .as_ref()
        .map_err(|_| anyhow!("attempt to verify attestation binding to a failed attestation"))?;

    for (verifier_id, binding_verifier) in &attestation.session_binding_verifiers {
        binding_verifier.verify_binding(
            handshake_hash,
            bindings
                .get(verifier_id)
                .ok_or(anyhow!("handshake message doesn't have a binding for ID {}", verifier_id))?
                .encode_to_vec()
                .as_slice(),
        )?;
    }
    Ok(())
}
