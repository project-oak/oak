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

use alloc::{boxed::Box, collections::VecDeque, vec::Vec};

use anyhow::{anyhow, Context, Error};
use oak_crypto::encryptor::Encryptor;
use oak_proto_rust::oak::session::v1::{
    session_request::Request, session_response::Response, SessionRequest, SessionResponse,
};

use crate::{
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
pub trait Session {
    /// Checks whether session is ready to send and receive encrypted messages.
    /// Session becomes ready once remote attestation and crypto handshake have
    /// been successfully finished.
    fn is_open(&self) -> bool;

    /// Encrypts `plaintext` and send it to the peer.
    ///
    /// This function can be called multiple times in a row, which will result
    /// in multiple outgoing protocol messages being created.
    fn write(&mut self, plaintext: &[u8]) -> anyhow::Result<()>;

    /// Reads an encrypted message from the peer and decrypt it.
    ///
    /// This function can be called multiple times in a row, if the peer sent
    /// multiple protocol messages that need to be decrypted.
    ///
    /// Method returns `Result<Option<()>>` with the corresponding outcomes:
    /// - `Ok(None)`: Nothing to read
    /// - `Ok(Some(Vec<u8>))`: Successfully read plaintext bytes
    /// - `Err`: Protocol error
    fn read(&mut self) -> anyhow::Result<Option<Vec<u8>>>;
}

// Client-side secure attested session entrypoint.
pub struct ClientSession {
    handshaker: ClientHandshaker,
    // encryptor is initialized once the handshake is completed and the session becomes open
    encryptor_config: EncryptorConfig,
    encryptor: Option<Box<dyn Encryptor>>,
    outgoing_requests: VecDeque<SessionRequest>,
    incoming_responses: VecDeque<SessionResponse>,
}

impl ClientSession {
    pub fn create(config: SessionConfig) -> Result<Self, Error> {
        Ok(Self {
            handshaker: ClientHandshaker::create(config.handshaker_config)
                .context("couldn't create the client handshaker")?,
            encryptor_config: config.encryptor_config,
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

    fn write(&mut self, plaintext: &[u8]) -> anyhow::Result<()> {
        if let Some(encryptor) = self.encryptor.as_mut() {
            let ciphertext = encryptor
                .encrypt(plaintext.into())
                .map(From::from)
                .context("couldn't encrypt the supplied plaintext")?;
            self.outgoing_requests
                .push_back(SessionRequest { request: Some(Request::Ciphertext(ciphertext)) });
            Ok(())
        } else {
            Err(anyhow!("the session is not open"))
        }
    }

    fn read(&mut self) -> anyhow::Result<Option<Vec<u8>>> {
        if let Some(encryptor) = self.encryptor.as_mut() {
            match self.incoming_responses.pop_front() {
                Some(response) => {
                    let ciphertext = match response.response {
                        Some(Response::Ciphertext(ciphertext)) => ciphertext,
                        _ => {
                            return Err(anyhow!(
                                "unexpected content of SessionResponse: no ciphertext set"
                            ));
                        }
                    };
                    Ok(Some(
                        encryptor
                            .decrypt(ciphertext.as_slice().into())
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
        if self.is_open() {
            return Ok(self.outgoing_requests.pop_front());
        };
        Ok(self
            .handshaker
            .get_outgoing_message()?
            .map(|h| SessionRequest { request: Some(Request::HandshakeRequest(h)) }))
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &SessionResponse,
    ) -> anyhow::Result<Option<()>> {
        if self.is_open() {
            return match incoming_message.response {
                Some(Response::Ciphertext(_)) => {
                    self.incoming_responses.push_back(incoming_message.clone());
                    Ok(Some(()))
                }
                _ => Err(anyhow!(
                    "unexpected content of SessionResponse: session open but no ciphertext set"
                )),
            };
        }
        match incoming_message.response.as_ref() {
            Some(Response::HandshakeResponse(handshake_message)) => {
                self.handshaker.put_incoming_message(handshake_message)?.ok_or(anyhow!(
                    "invalid session state: handshake message received but handshaker doesn't
                    expect any"
                ))?;
                if let Some(session_keys) = self.handshaker.derive_session_keys() {
                    self.encryptor = Some(
                        (self.encryptor_config.encryptor_provider)(session_keys)
                            .context("couldn't create an encryptor from the session key")?,
                    )
                }
                Ok(Some(()))
            }
            _ => Err(anyhow!("unexpected content of session response")),
        }
    }
}

// Server-side secure attested session entrypoint.
pub struct ServerSession {
    handshaker: ServerHandshaker,
    // encryptor is initialized once the handshake is completed and the session becomes open
    encryptor_config: EncryptorConfig,
    encryptor: Option<Box<dyn Encryptor>>,
    outgoing_responses: VecDeque<SessionResponse>,
    incoming_requests: VecDeque<SessionRequest>,
}

impl ServerSession {
    pub fn new(config: SessionConfig) -> Self {
        Self {
            handshaker: ServerHandshaker::new(config.handshaker_config),
            encryptor_config: config.encryptor_config,
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

    fn write(&mut self, plaintext: &[u8]) -> anyhow::Result<()> {
        if let Some(encryptor) = self.encryptor.as_mut() {
            let ciphertext = encryptor
                .encrypt(plaintext.into())
                .map(From::from)
                .context("couldn't encrypt the supplied plaintext")?;
            self.outgoing_responses
                .push_back(SessionResponse { response: Some(Response::Ciphertext(ciphertext)) });
            Ok(())
        } else {
            Err(anyhow!("the session is not open"))
        }
    }

    fn read(&mut self) -> anyhow::Result<Option<Vec<u8>>> {
        if let Some(encryptor) = self.encryptor.as_mut() {
            match self.incoming_requests.pop_front() {
                Some(request) => {
                    let ciphertext = match request.request {
                        Some(Request::Ciphertext(ciphertext)) => ciphertext,
                        _ => {
                            return Err(anyhow!(
                                "unexpected content of SessionRequest: no ciphertext set"
                            ));
                        }
                    };
                    Ok(Some(
                        encryptor
                            .decrypt(ciphertext.as_slice().into())
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
        Ok(self.outgoing_responses.pop_front())
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &SessionRequest,
    ) -> anyhow::Result<Option<()>> {
        if self.is_open() {
            return match incoming_message.request {
                Some(Request::Ciphertext(_)) => {
                    self.incoming_requests.push_back(incoming_message.clone());
                    Ok(Some(()))
                }
                _ => Err(anyhow!(
                    "unexpected content of SessionRequest: session open but no ciphertext set"
                )),
            };
        }
        match incoming_message.request.as_ref() {
            Some(Request::HandshakeRequest(handshake_message)) => {
                self.handshaker.put_incoming_message(handshake_message)?.ok_or(anyhow!(
                    "invalid session state: handshake message received but handshaker doesn't
                     expect any"
                ))?;
                if let Some(outgoing_message) = self.handshaker.get_outgoing_message()? {
                    self.outgoing_responses.push_back(SessionResponse {
                        response: Some(Response::HandshakeResponse(outgoing_message)),
                    });
                }
                if let Some(session_keys) = self.handshaker.derive_session_keys() {
                    self.encryptor = Some(
                        (self.encryptor_config.encryptor_provider)(session_keys)
                            .context("couldn't create an encryptor from the session key")?,
                    )
                }
                Ok(Some(()))
            }
            _ => Err(anyhow!("unexpected content of session request")),
        }
    }
}
