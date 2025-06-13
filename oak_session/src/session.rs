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
//! two parties. It orchestrates the complex process of establishing a trusted
//! and confidential communication channel, suitable for sensitive interactions.
//!
//! ## Overview
//!
//! The primary goal of this module is to simplify the creation of sessions that
//! are:
//! - **Attested**: Both parties can cryptographically verify the identity and
//!   trustworthiness of the other, based on evidence and endorsements. This is
//!   handled by the `AttestationHandler` implementations.
//! - **End-to-End Encrypted**: Application messages exchanged over the session
//!   are encrypted using the derived session keys, ensuring confidentiality and
//!   integrity. This is the responsibility of the `Encryptor`. The keying
//!   material is obtained from the `HandshakeHandler` during the handshake
//!   phase, using the Noise Protocol Framework.
//! - **Bound**: The attestation and handshake phases are cryptographically
//!   linked, ensuring that the attested peer is the same one participating in
//!   the handshake. `SessionBindingToken`s allow applications to further bind
//!   their operations to this specific secure session.
//!
//! ## Design Philosophy
//!
//! The session establishment is a multi-step process. To manage this complexity
//! and ensure protocol correctness, the module employs a state machine pattern,
//! represented by the `Step` enum. This design:
//! - Enforces the correct sequence of operations (Attestation -> Handshake ->
//!   Open).
//! - Manages the lifecycle and ownership of state-specific components (like
//!   `AttestationHandler`, `HandshakeHandler`, `Encryptor`).
//! - Facilitates clear transitions and error handling at each step.
//!
//! The `Session` trait provides a high-level API for applications, abstracting
//! away the internal state transitions. The `ProtocolEngine` trait is used by
//! the `Session` implementations to drive the underlying message exchange for
//! each phase of the protocol. This separation of concerns makes the system
//! modular and easier to manage.
//!
//! Client (`ClientSession`) and server (`ServerSession`) roles have distinct
//! implementations, reflecting their different responsibilities in the protocol
//! initiation and response flow.

use alloc::{
    boxed::Box,
    collections::{BTreeMap, VecDeque},
    string::String,
    sync::Arc,
    vec::Vec,
};
use core::mem;

use anyhow::{anyhow, Context, Error, Ok};
use oak_crypto::{encryptor::Encryptor, noise_handshake::session_binding_token_hash};
use oak_proto_rust::oak::session::v1::{
    session_request::Request, session_response::Response, EncryptedMessage, PlaintextMessage,
    SessionBinding, SessionRequest, SessionResponse,
};

use crate::{
    attestation::{
        AttestationHandler, AttestationVerdict, ClientAttestationHandler, ServerAttestationHandler,
        VerifierResult,
    },
    config::{EncryptorProvider, SessionConfig},
    handshake::{
        ClientHandshakeHandler, ClientHandshakeHandlerBuilder, HandshakeHandler,
        HandshakeHandlerBuilder, ServerHandshakeHandler, ServerHandshakeHandlerBuilder,
    },
    session_binding::SessionBindingVerifierProvider,
    ProtocolEngine,
};

/// A unique identifier for an established secure session channel.
///
/// This token is derived from the cryptographic hash of the handshake
/// transcript and an `info` string. It can be used by applications to bind
/// other operations or resources to this specific secure session, providing a
/// strong link to the authenticated and encrypted channel.
pub struct SessionBindingToken(Vec<u8>);

impl SessionBindingToken {
    /// Creates a new `SessionBindingToken`.
    ///
    /// `handshake_hash` is the hash of the completed Noise handshake
    /// transcript. `info` is an optional byte string provided by the
    /// application, allowing for context-specific tokens (e.g.,
    /// differentiating tokens for different purposes within the same
    /// session).
    pub fn new(handshake_hash: &[u8], info: &[u8]) -> Self {
        let hash = session_binding_token_hash(handshake_hash, info);
        Self(hash.to_vec())
    }

    /// Returns a slice view of the token's bytes.
    /// The lifetime of the slice is bound to the `SessionBindingToken`
    /// instance.
    pub fn as_slice(&self) -> &[u8] {
        self.0.as_slice()
    }

    /// Clones the token and returns its bytes as a boxed slice.
    ///
    /// This is useful when the token needs to be stored with a `'static`
    /// lifetime or moved elsewhere.
    pub fn into_boxed_slice(&self) -> Box<[u8]> {
        self.0.clone().into_boxed_slice()
    }
}

/// Trait defining the interface for an end-to-end encrypted, attested,
/// bidirectional streaming session.
///
/// This is the primary API for applications using the Oak Session SDK.
/// Implementations manage the full lifecycle of a session: attestation,
/// cryptographic handshake, and secure data exchange.
///
/// If any method returns an `Error`, the session is considered compromised or
/// in an error and a new session needs to be started (because the state-machine
/// is in an incorrect state).
pub trait Session: Send {
    /// Checks if the session is open and ready for secure communication.
    ///
    /// A session becomes open only after both the remote attestation (if
    /// configured) and the cryptographic handshake have completed
    /// successfully.
    fn is_open(&self) -> bool;

    /// Encrypts the given `plaintext` message and prepares it for sending to
    /// the peer.
    ///
    /// This method should only be called when `is_open()` returns true.
    /// The encrypted message is queued internally and will be wrapped in a
    /// `SessionRequest` (for clients) or `SessionResponse` (for servers) when
    /// `get_outgoing_message()` is called.
    ///
    /// Multiple calls to `write` can queue multiple messages.
    fn write(&mut self, plaintext: PlaintextMessage) -> Result<(), Error>;

    /// Reads an encrypted message from the peer and decrypt it.
    ///
    /// This method should only be called when `is_open()` returns true.
    /// This function can be called multiple times in a row, if the peer sent
    /// multiple protocol messages that need to be decrypted (previously
    /// supplied via `put_incoming_message()`).
    ///
    /// Method returns `Result<Option<()>>` with the corresponding outcomes:
    /// - `Ok(Some(PlaintextMessage))`: If a message was successfully decrypted.
    /// - `Ok(None)`: If there are no pending incoming messages to decrypt.
    /// - `Err(Error)`: If a decryption or protocol error occurs.
    fn read(&mut self) -> Result<Option<PlaintextMessage>, Error>;

    /// Returns a unique `SessionBindingToken` for this session.
    ///
    /// This token can be used by the application to bind other data or
    /// operations to the security properties (authentication, encryption)
    /// of this specific session. `info_string` allows for domain separation
    /// if multiple tokens are needed for different purposes within the same
    /// session.
    ///
    /// This method can only be called successfully when `is_open()` is true.
    fn get_session_binding_token(&self, info_string: &[u8]) -> Result<SessionBindingToken, Error>;
}

/// Represents the internal state machine and data for a session's progression.
///
/// This enum encapsulates the distinct phases of establishing a secure session:
/// Attestation, Handshake, and Open (for active communication). It manages the
/// ownership and transition of state-specific objects like
/// `AttestationHandler`, `HandshakeHandler`, and `Encryptor`. The `Invalid`
/// state is a temporary placeholder used during non-atomic state transitions to
/// maintain memory safety.
///
/// `AP` is the type of `AttestationHandler` (client or server).
/// `H` is the type of `HandshakeHandler` (client or server).
/// for transition to the next one. It is parametrized by the type of
/// attestation provider and handshaker (either the client or server version).
enum Step<AP: AttestationHandler, H: HandshakeHandler> {
    /// Protocol step where communicating parties exchange and verify the
    /// attested evidence. May be skipped if no attestation is required.
    ///
    /// Holds the `attester` for managing this phase, a
    /// `handshake_handler_provider` to create the `HandshakeHandler` for
    /// the next phase, and an `encryptor_provider` to create the
    /// `Encryptor` once the handshake is complete. The lifetimes of these
    /// providers are managed by the `Step` enum.
    Attestation {
        attester: AP,
        handshake_handler_provider: Box<dyn HandshakeHandlerBuilder<H>>,
        encryptor_provider: Box<dyn EncryptorProvider>,
    },
    /// Protocol step for performing the Noise handshake.
    ///
    /// Holds the active `handshaker`, the `encryptor_provider`, and the
    /// `attestation_results` obtained from the previous phase. These results
    /// may be used for verifying session bindings during the handshake.
    Handshake {
        handshaker: H,
        encryptor_provider: Box<dyn EncryptorProvider>,
        attestation_results: BTreeMap<String, VerifierResult>,
    },
    /// The phase where the session is established and ready for encrypted
    /// communication.
    ///
    /// Holds the `encryptor` for protecting application messages and the
    /// `handshake_hash` from the completed handshake, used for generating
    /// `SessionBindingToken`s. The `Encryptor`'s lifetime is tied to this
    /// state.
    Open { encryptor: Box<dyn Encryptor>, handshake_hash: Vec<u8> },
    /// A temporary state indicating that the session is currently transitioning
    /// between valid steps. Operations on a session in this state will fail.
    Invalid,
}

impl<AP: AttestationHandler, H: HandshakeHandler> Step<AP, H> {
    /// Transitions the session to the next logical step in the protocol.
    ///
    /// - From `Attestation` to `Handshake`: Occurs after
    ///   `attester.take_attestation_verdict()` is successful. The
    ///   `HandshakeHandler` is built using `handshake_handler_provider`.
    /// - From `Handshake` to `Open`: Occurs after
    ///   `handshaker.take_session_keys()` is successful. The `Encryptor` is
    ///   built using `encryptor_provider`.
    ///
    /// This method manages the ownership transfer of data (like
    /// `AttestationResults` to `Handshake` step, and `SessionKeys` to the
    /// `Encryptor`). If a transition fails (e.g., attestation failed, or
    /// provider fails to build), an error is returned, and the session
    /// typically remains in `Invalid` or the previous state if the
    /// transition was aborted early.
    fn next(&mut self) -> Result<(), Error> {
        // We can't transition between states without using this temp variable while
        // ensuring the memory safety because of the objects' lifetime.
        let old_state = mem::replace(self, Step::Invalid);
        match old_state {
            Step::Attestation { attester, handshake_handler_provider, encryptor_provider } => {
                let attestation_results = match attester.take_attestation_verdict()? {
                    AttestationVerdict::AttestationPassed { attestation_results } => {
                        attestation_results
                    }
                    AttestationVerdict::AttestationFailed { reason, .. } => {
                        return Err(anyhow!("attestation failed: {:?}", reason));
                    }
                };
                // The peer bindings are expected whenever the peer provides evidence that can
                // be bound to the session. Even if the evidence hasn't been verified the peer
                // is expected (and required) to send the bindings for the evidence that it
                // supplies.
                let expect_peer_bindings = attestation_results.iter().any(|(_, v)| match v {
                    VerifierResult::Success(_)
                    | VerifierResult::Failure(_)
                    | VerifierResult::Unverified(_) => true,
                    VerifierResult::Missing => false,
                });
                *self = Step::Handshake {
                    encryptor_provider,
                    handshaker: handshake_handler_provider.build(expect_peer_bindings)?,
                    attestation_results,
                };
            }
            Step::Handshake { handshaker, encryptor_provider, .. } => {
                *self = Step::Open {
                    handshake_hash: handshaker.get_handshake_hash()?.to_vec(),
                    encryptor: encryptor_provider
                        .provide_encryptor(handshaker.take_session_keys()?)?,
                };
            }
            Step::Open { .. } => {
                return Err(anyhow!("there is no next step when the session is open"))
            }
            Step::Invalid => return Err(anyhow!("session is currently in an invalid state")),
        };
        Ok(())
    }

    /// Retrieves a `SessionBindingToken` if the session is in the `Open` state.
    ///
    /// Delegates to `SessionBindingToken::new` using the stored
    /// `handshake_hash`. Returns an error if the session is not yet open.
    fn get_session_binding_token(&self, info: &[u8]) -> Result<SessionBindingToken, Error> {
        match &self {
            Step::Open { handshake_hash, .. } => Ok(SessionBindingToken::new(handshake_hash, info)),
            _ => Err(anyhow!("the session is not open")),
        }
    }
}

/// Client-side implementation of an end-to-end secure attested session.
///
/// Orchestrates the `ClientAttestationHandler` and `ClientHandshakeHandler`
/// through the `Step` state machine to establish a session with a server.
/// Implements the `Session` trait for application use and `ProtocolEngine` for
/// driving the underlying message exchange.
pub struct ClientSession {
    /// The current step/state of the session establishment process.
    step: Step<ClientAttestationHandler, ClientHandshakeHandler>,
    /// Providers for creating `SessionBindingVerifier`s, keyed by attestation
    /// ID. Used to verify session bindings received from the server during
    /// the handshake, linking the server's attestation to the current
    /// session.
    binding_verifier_providers: BTreeMap<String, Arc<dyn SessionBindingVerifierProvider>>,
    /// Queue for outgoing `SessionRequest` messages (typically encrypted
    /// application data).
    outgoing_requests: VecDeque<SessionRequest>,
    /// Queue for incoming `SessionResponse` messages that have been processed
    /// up to the session layer but not yet decrypted and read by the
    /// application.
    incoming_responses: VecDeque<SessionResponse>,
}

impl ClientSession {
    /// Creates a new `ClientSession` with the given `SessionConfig`.
    ///
    /// Initializes the session in the `Step::Attestation` phase, creating a
    /// `ClientAttestationHandler`. The configuration is consumed, and its
    /// components (like providers and keys) are moved into the session's
    /// state. The lifetimes of objects within `config` (e.g., keys in
    /// `HandshakeHandlerConfig`) are now managed by the `ClientSession`.
    pub fn create(config: SessionConfig) -> Result<Self, Error> {
        Ok(Self {
            step: Step::Attestation {
                attester: ClientAttestationHandler::create(config.attestation_handler_config)?,
                handshake_handler_provider: Box::new(ClientHandshakeHandlerBuilder {
                    config: config.handshake_handler_config,
                }),
                encryptor_provider: config.encryptor_config.encryptor_provider,
            },
            binding_verifier_providers: config.binding_verifier_providers,
            outgoing_requests: VecDeque::new(),
            incoming_responses: VecDeque::new(),
        })
    }
}

impl Session for ClientSession {
    /// Checks if the client session is open. See `Session::is_open`.
    fn is_open(&self) -> bool {
        matches!(self.step, Step::Open { .. })
    }

    /// Encrypts and queues a message for the server. See `Session::write`.
    fn write(&mut self, plaintext: PlaintextMessage) -> Result<(), Error> {
        match &mut self.step {
            Step::Open { encryptor, .. } => {
                let encrypted_message: EncryptedMessage = encryptor
                    .encrypt(plaintext.into())
                    .map(From::from)
                    .context("couldn't encrypt the supplied plaintext")?;
                self.outgoing_requests.push_back(SessionRequest {
                    request: Some(Request::EncryptedMessage(encrypted_message)),
                });
                Ok(())
            }
            _ => Err(anyhow!("the session is not open")),
        }
    }

    /// Reads and decrypts a message from the server. See `Session::read`.
    fn read(&mut self) -> Result<Option<PlaintextMessage>, Error> {
        match &mut self.step {
            Step::Open { encryptor, .. } => match self.incoming_responses.pop_front() {
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
                            .decrypt(encrypted_message.into())
                            .map(From::from)
                            .context("couldn't decrypt the supplied plaintext")?,
                    ))
                }
                None => Ok(None),
            },
            _ => Err(anyhow!("the session is not open")),
        }
    }

    /// Gets a session binding token. See `Session::get_session_binding_token`.
    fn get_session_binding_token(&self, info_string: &[u8]) -> Result<SessionBindingToken, Error> {
        self.step.get_session_binding_token(info_string)
    }
}

impl ProtocolEngine<SessionResponse, SessionRequest> for ClientSession {
    /// Gets the next outgoing `SessionRequest` to be sent to the server.
    ///
    /// Depending on the current `step`:
    /// - `Attestation`: Returns an `AttestRequest` from the
    ///   `ClientAttestationHandler`.
    /// - `Handshake`: Returns a `HandshakeRequest` from the
    ///   `ClientHandshakeHandler`. If the handshake completes as a result,
    ///   transitions to `Open`.
    /// - `Open`: Returns an `EncryptedMessage` (application data) from
    ///   `outgoing_requests`.
    ///
    /// If no message is ready, returns `Ok(None)`.
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
            Step::Open { .. } => {}
            Step::Invalid => return Err(anyhow!("session is in an invalid state")),
        }

        Ok(self.outgoing_requests.pop_front())
    }

    /// Processes an incoming `SessionResponse` from the server.
    ///
    /// Depending on the current `step` and message type:
    /// - `Attestation` + `AttestResponse`: Passes to
    ///   `ClientAttestationHandler`. If attestation completes, transitions to
    ///   `Handshake`.
    /// - `Handshake` + `HandshakeResponse`: Passes to `ClientHandshakeHandler`.
    ///   Verifies server's session bindings using `binding_verifier_providers`
    ///   and `attestation_results`. If handshake completes, transitions to
    ///   `Open`.
    /// - `Open` + `EncryptedMessage`: Queues in `incoming_responses` for
    ///   `read()`.
    ///
    /// Returns `Ok(Some(()))` if processed, `Err` on mismatch or protocol
    /// error.
    fn put_incoming_message(
        &mut self,
        incoming_message: SessionResponse,
    ) -> Result<Option<()>, Error> {
        match (incoming_message, &mut self.step) {
            (
                SessionResponse { response: Some(Response::AttestResponse(attest_message)) },
                Step::Attestation { attester, .. },
            ) => {
                attester.put_incoming_message(attest_message)?.ok_or(anyhow!(
                    "invalid session state: attest message received but attester doesn't expect
                     any"
                ))?;
                self.step.next()?;
                Ok(Some(()))
            }
            (
                SessionResponse { response: Some(Response::HandshakeResponse(handshake_message)) },
                Step::Handshake { handshaker, attestation_results, .. },
            ) => {
                let bindings = handshake_message.attestation_bindings.clone();
                handshaker.put_incoming_message(handshake_message)?.ok_or(anyhow!(
                    "invalid session state: handshake message received but handshaker doesn't
                     expect any"
                ))?;
                verify_session_binding(
                    &self.binding_verifier_providers,
                    attestation_results,
                    &bindings,
                    handshaker.get_handshake_hash()?,
                )?;
                if handshaker.is_handshake_complete() {
                    self.step.next()?;
                }
                Ok(Some(()))
            }
            (
                im @ SessionResponse { response: Some(Response::EncryptedMessage(_)) },
                Step::Open { .. },
            ) => {
                self.incoming_responses.push_back(im);
                Ok(Some(()))
            }
            (_, _) => Err(anyhow!("unexpected content of session response")),
        }
    }
}

/// Server-side implementation of an end-to-end secure attested session.
///
/// Orchestrates the `ServerAttestationHandler` and `ServerHandshakeHandler`
/// through the `Step` state machine to establish a session with a client.
/// Implements the `Session` trait for application use and `ProtocolEngine` for
/// driving the underlying message exchange.
pub struct ServerSession {
    /// The current step/state of the session establishment process.
    step: Step<ServerAttestationHandler, ServerHandshakeHandler>,
    /// Providers for creating `SessionBindingVerifier`s, keyed by attestation
    /// ID. Used to verify session bindings received from the client during
    /// the handshake, linking the client's attestation to the current
    /// session.
    binding_verifier_providers: BTreeMap<String, Arc<dyn SessionBindingVerifierProvider>>,
    /// Queue for outgoing `SessionResponse` messages (typically encrypted
    /// application data).
    outgoing_responses: VecDeque<SessionResponse>,
    /// Queue for incoming `SessionRequest` messages that have been processed up
    /// to the session layer but not yet decrypted and read by the
    /// application.
    incoming_requests: VecDeque<SessionRequest>,
}

impl ServerSession {
    /// Creates a new `ServerSession` with the given `SessionConfig`.
    ///
    /// Initializes the session in the `Step::Attestation` phase, creating a
    /// `ServerAttestationHandler`. Determines if client binding is expected
    /// based on `config.attestation_handler_config.attestation_type` for
    /// the `ServerHandshakeHandler`. The configuration is consumed.
    pub fn create(config: SessionConfig) -> Result<Self, Error> {
        Ok(Self {
            step: Step::Attestation {
                attester: ServerAttestationHandler::create(config.attestation_handler_config)?,
                handshake_handler_provider: Box::new(ServerHandshakeHandlerBuilder {
                    config: config.handshake_handler_config,
                }),
                encryptor_provider: config.encryptor_config.encryptor_provider,
            },
            binding_verifier_providers: config.binding_verifier_providers,
            outgoing_responses: VecDeque::new(),
            incoming_requests: VecDeque::new(),
        })
    }
}

impl Session for ServerSession {
    /// Checks if the server session is open. See `Session::is_open`.
    fn is_open(&self) -> bool {
        matches!(self.step, Step::Open { .. })
    }

    /// Encrypts and queues a message for the client. See `Session::write`.
    fn write(&mut self, plaintext: PlaintextMessage) -> Result<(), Error> {
        match &mut self.step {
            Step::Open { encryptor, .. } => {
                let encrypted_message: EncryptedMessage = encryptor
                    .encrypt(plaintext.into())
                    .map(From::from)
                    .context("couldn't encrypt the supplied plaintext")?;
                self.outgoing_responses.push_back(SessionResponse {
                    response: Some(Response::EncryptedMessage(encrypted_message)),
                });
                Ok(())
            }
            _ => Err(anyhow!("the session is not open")),
        }
    }

    /// Reads and decrypts a message from the client. See `Session::read`.
    fn read(&mut self) -> Result<Option<PlaintextMessage>, Error> {
        match &mut self.step {
            Step::Open { encryptor, .. } => match self.incoming_requests.pop_front() {
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
                            .decrypt(encrypted_message.into())
                            .map(From::from)
                            .context("couldn't decrypt the supplied plaintext")?,
                    ))
                }
                None => Ok(None),
            },
            _ => Err(anyhow!("the session is not open")),
        }
    }

    /// Gets a session binding token. See `Session::get_session_binding_token`.
    fn get_session_binding_token(&self, info_string: &[u8]) -> Result<SessionBindingToken, Error> {
        self.step.get_session_binding_token(info_string)
    }
}

impl ProtocolEngine<SessionRequest, SessionResponse> for ServerSession {
    /// Gets the next outgoing `SessionResponse` to be sent to the client.
    ///
    /// Depending on the current `step`:
    /// - `Attestation`: Returns an `AttestResponse` from
    ///   `ServerAttestationHandler` (after processing client's request).
    ///   Transitions to `Handshake`.
    /// - `Handshake`: Returns a `HandshakeResponse` from
    ///   `ServerHandshakeHandler`. If handshake completes, transitions to
    ///   `Open`.
    /// - `Open`: Returns an `EncryptedMessage` (application data) from
    ///   `outgoing_responses`.
    ///
    /// If no message is ready, returns `Ok(None)`.
    fn get_outgoing_message(&mut self) -> Result<Option<SessionResponse>, Error> {
        match &mut self.step {
            Step::Attestation { attester, .. } => {
                if let Some(attest_message) = attester.get_outgoing_message()? {
                    self.step.next()?;
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
            Step::Open { .. } => Ok(self.outgoing_responses.pop_front()),
            Step::Invalid => Err(anyhow!("session is in an invalid state")),
        }
    }

    /// Processes an incoming `SessionRequest` from the client.
    ///
    /// Depending on the current `step` and message type:
    /// - `Attestation` + `AttestRequest`: Passes to `ServerAttestationHandler`.
    /// - `Handshake` + `HandshakeRequest`: Passes to `ServerHandshakeHandler`.
    ///   If this is the client's binding follow-up, verifies it using
    ///   `binding_verifier_providers` and `attestation_results`. If handshake
    ///   completes, transitions to `Open`.
    /// - `Open` + `EncryptedMessage`: Queues in `incoming_requests` for
    ///   `read()`.
    ///
    /// Returns `Ok(Some(()))` if processed, `Err` on mismatch or protocol
    /// error.
    fn put_incoming_message(
        &mut self,
        incoming_message: SessionRequest,
    ) -> Result<Option<()>, Error> {
        match (incoming_message, &mut self.step) {
            (
                SessionRequest { request: Some(Request::AttestRequest(attest_message)) },
                Step::Attestation { attester, .. },
            ) => {
                attester.put_incoming_message(attest_message)?.ok_or(anyhow!(
                    "invalid session state: attest message received but attester doesn't expect any"
                ))?;
                Ok(Some(()))
            }
            (
                SessionRequest { request: Some(Request::HandshakeRequest(handshake_message)) },
                Step::Handshake { handshaker, attestation_results, .. },
            ) => {
                let bindings = handshake_message.attestation_bindings.clone();
                handshaker.put_incoming_message(handshake_message)?.ok_or(anyhow!(
                    "invalid session state: handshake message received but handshaker doesn't
                     expect any"
                ))?;
                if handshaker.is_handshake_complete() {
                    verify_session_binding(
                        &self.binding_verifier_providers,
                        attestation_results,
                        &bindings,
                        handshaker.get_handshake_hash()?,
                    )?;
                }
                Ok(Some(()))
            }
            (
                im @ SessionRequest { request: Some(Request::EncryptedMessage(_)) },
                Step::Open { .. },
            ) => {
                self.incoming_requests.push_back(im);
                Ok(Some(()))
            }
            (_, _) => Err(anyhow!("unexpected content of session request")),
        }
    }
}

/// Verifies the received session `bindings` against the provided
/// `attestation_results`.
///
/// For each successful verification in `attestation_results` (keyed by
/// attestation ID), this function:
/// 1. Retrieves the corresponding `SessionBindingVerifierProvider` from
///    `binding_verifier_providers`.
/// 2. Creates a `SessionBindingVerifier` using the attestation result.
/// 3. Retrieves the corresponding `SessionBinding` from the `bindings` map.
/// 4. Calls `verify_binding` on the verifier with the `handshake_hash` and the
///    received binding.
///
/// This ensures that for each attested identity (via `attestation_results`),
/// its purported binding to the current session (via `handshake_hash`) is
/// cryptographically valid. An error is returned if any verification fails, or
/// if providers/bindings are missing.
fn verify_session_binding(
    binding_verifier_providers: &BTreeMap<String, Arc<dyn SessionBindingVerifierProvider>>,
    attestation_results: &BTreeMap<String, VerifierResult>,
    bindings: &BTreeMap<String, SessionBinding>,
    handshake_hash: &[u8],
) -> Result<(), Error> {
    for (verifier_id, result) in attestation_results {
        if let VerifierResult::Success(r) = result {
            let binding_verifier = binding_verifier_providers
                .get(verifier_id)
                .ok_or(anyhow!(
                "no session binding verifier provider supplied for the verifier ID {verifier_id}"
            ))?
                .create_session_binding_verifier(r)?;
            binding_verifier.verify_binding(
                handshake_hash,
                bindings
                    .get(verifier_id)
                    .ok_or(anyhow!(
                        "handshake message doesn't have a binding for ID {verifier_id}"
                    ))?
                    .binding
                    .as_slice(),
            )?;
        }
    }
    Ok(())
}
