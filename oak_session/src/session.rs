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

use alloc::{boxed::Box, vec::Vec};

use anyhow::{anyhow, Context, Error};
use oak_crypto::encryptor::Encryptor;
use oak_proto_rust::oak::session::v1::{
    session_request::Request, session_response::Response, SessionRequest, SessionResponse,
};

use crate::{
    config::SessionConfig,
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
#[allow(dead_code)]
pub struct ClientSession<'a> {
    config: &'a SessionConfig<'a>,
    handshaker: ClientHandshaker,
    encryptor: Option<Box<dyn Encryptor>>,
    outgoing_requests: Vec<SessionRequest>,
    incoming_responses: Vec<SessionResponse>,
}

#[allow(dead_code)]
impl<'a> ClientSession<'a> {
    pub fn create(config: &'a SessionConfig<'a>) -> Result<Self, Error> {
        Ok(Self {
            config,
            handshaker: ClientHandshaker::create(&config.handshaker_config)
                .context("couldn't create the client handshaker")?,
            encryptor: None,
            outgoing_requests: vec![],
            incoming_responses: vec![],
        })
    }
}

impl<'a> Session for ClientSession<'a> {
    fn is_open(&self) -> bool {
        self.encryptor.is_some()
    }

    fn write(&mut self, plaintext: &[u8]) -> anyhow::Result<()> {
        match &mut self.encryptor {
            Some(encryptor) => {
                let ciphertext = encryptor
                    .encrypt(plaintext.into())
                    .context("couldn't encrypt the supplied plaintext")?;
                self.outgoing_requests
                    .push(SessionRequest { r#request: Some(Request::Ciphertext(ciphertext)) });
                Ok(())
            }
            None => Err(anyhow!("the session is not open")),
        }
    }

    fn read(&mut self) -> anyhow::Result<Option<Vec<u8>>> {
        match (&mut self.encryptor, self.incoming_responses.pop()) {
            (Some(encryptor), Some(response)) => {
                let ciphertext = match response.r#response {
                    Some(Response::Ciphertext(ciphertext)) => ciphertext,
                    _ => return Err(anyhow!("unexpected content of SessionResponse")),
                };
                Ok(Some(
                    encryptor
                        .decrypt(ciphertext.as_slice().into())
                        .context("couldn't encrypt the supplied plaintext")?,
                ))
            }
            (_, None) => Ok(None),
            (None, _) => Err(anyhow!("the session is not open")),
        }
    }
}

impl<'a> ProtocolEngine<SessionResponse, SessionRequest> for ClientSession<'a> {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<SessionRequest>> {
        if self.is_open() {
            return Ok(self.outgoing_requests.pop());
        };
        Ok(self
            .handshaker
            .get_outgoing_message()?
            .map(|h| SessionRequest { r#request: Some(Request::HandshakeRequest(h)) }))
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &SessionResponse,
    ) -> anyhow::Result<Option<()>> {
        if self.is_open() {
            self.incoming_responses.push(incoming_message.clone());
            return Ok(Some(()));
        }
        match incoming_message.r#response.as_ref() {
            Some(Response::HandshakeResponse(handshake_message)) => {
                let result = self.handshaker.put_incoming_message(handshake_message);
                if let Some(session_keys) = self.handshaker.derive_session_keys() {
                    self.encryptor = Some(
                        (self.config.encryptor_config.encryptor_provider)(session_keys)
                            .context("couldn't create an encryptor from the session key")?,
                    )
                }
                result
            }
            _ => Err(anyhow!("unexpected content of session response")),
        }
    }
}

// Server-side secure attested session entrypoint.
#[allow(dead_code)]
pub struct ServerSession<'a> {
    config: &'a SessionConfig<'a>,
    handshaker: ServerHandshaker<'a>,
}

#[allow(dead_code)]
impl<'a> ServerSession<'a> {
    pub fn new(config: &'a SessionConfig<'a>) -> Self {
        Self { config, handshaker: ServerHandshaker::new(&config.handshaker_config) }
    }
}

impl<'a> Session for ServerSession<'a> {
    fn is_open(&self) -> bool {
        core::unimplemented!();
    }

    fn write(&mut self, _plaintext: &[u8]) -> anyhow::Result<()> {
        core::unimplemented!();
    }

    fn read(&mut self) -> anyhow::Result<Option<Vec<u8>>> {
        core::unimplemented!();
    }
}

impl<'a> ProtocolEngine<SessionRequest, SessionResponse> for ClientSession<'a> {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<SessionResponse>> {
        core::unimplemented!();
    }

    fn put_incoming_message(
        &mut self,
        _incoming_message: &SessionRequest,
    ) -> anyhow::Result<Option<()>> {
        core::unimplemented!();
    }
}
