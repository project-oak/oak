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
use oak_proto_rust::oak::{
    attestation::v1::Assertion,
    session::v1::{
        session_request::Request, session_response::Response, EncryptedMessage, EndorsedEvidence,
        PlaintextMessage, SessionBinding, SessionRequest, SessionResponse,
    },
};

use crate::{
    attestation::{
        AttestationHandler, AttestationState, ClientAttestationHandler, PeerAttestationVerdict,
        ServerAttestationHandler, VerifierResult,
    },
    config::{EncryptorProvider, SessionConfig},
    handshake::{
        ClientHandshakeHandler, ClientHandshakeHandlerBuilder, HandshakeHandler,
        HandshakeHandlerBuilder, HandshakeState, ServerHandshakeHandler,
        ServerHandshakeHandlerBuilder,
    },
    session_binding::{create_session_binding_token, SessionBindingVerifier},
    verifier::BoundAssertionVerifierResult,
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
    /// `handshake_binding_token` is the hash of the completed Noise handshake
    /// transcript. `info` is an optional byte string provided by the
    /// application, allowing for context-specific tokens (e.g.,
    /// differentiating tokens for different purposes within the same
    /// session).
    pub fn new(handshake_binding_token: &[u8], info: &[u8]) -> Self {
        let hash = session_binding_token_hash(handshake_binding_token, info);
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

/// Represents the evidence supplied by the peer during the attestation phase.
///
/// This evidence is used to verify the peer's identity and trustworthiness.
#[derive(Debug, Default, PartialEq)]
pub struct AttestationEvidence {
    /// The evidence supplied by the peer (in the legacy format).
    ///
    /// The key is the ID of the evidence, and the value is the evidence itself.
    pub evidence: BTreeMap<String, EndorsedEvidence>,
    /// The peer-provided bindings to the evidence.
    pub evidence_bindings: BTreeMap<String, SessionBinding>,
    // The evidence provided by the peer as assertions.
    pub assertions: BTreeMap<String, Assertion>,
    /// The peer-provided assertion bindings.
    pub assertion_bindings: BTreeMap<String, SessionBinding>,
    /// The hash of the handshake transcript.
    pub handshake_hash: Vec<u8>,
}

/// An [`AttestationPublisher`] can be added to a session configuration to allow
/// publishing received evidence to an external component.
pub trait AttestationPublisher: Send + Sync {
    /// The session will call this method once the session has been established.
    ///
    /// Keep in mind that the function will be called from the session state
    /// machine execution thread. So, implementation of a publisher should not
    /// perform any long-running or blocking operations. In most cases, the best
    /// approach is to queue the provided [`AttestationEvidence`] for eventual
    /// processing.
    fn publish(&self, attestation_evidence: AttestationEvidence);
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

    /// Returns the attestation evidence for this session, as supplied by the
    /// peer.
    ///
    /// This method can only be called successfully when `is_open()` is true.
    fn get_peer_attestation_evidence(&self) -> Result<AttestationEvidence, Error>;
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
        attestation_publisher: Option<Arc<dyn AttestationPublisher>>,
    },
    /// Protocol step for performing the Noise handshake.
    ///
    /// Holds the active `handshaker`, the `encryptor_provider`, and the
    /// `attestation_results` obtained from the previous phase. These results
    /// may be used for verifying session bindings during the handshake.
    Handshake {
        handshaker: H,
        encryptor_provider: Box<dyn EncryptorProvider>,
        attestation_publisher: Option<Arc<dyn AttestationPublisher>>,
    },
    /// The phase where the session is established and ready for encrypted
    /// communication.
    ///
    /// Holds the internal state of an open session:
    /// - `encryptor` for protecting application messages
    /// - `attestation_results` from the previous phase, used for verifying
    ///   session bindings during the handshake.
    /// - `handshake_binding_token` from the completed handshake, used for
    ///   generating `SessionBindingToken`s.
    Open {
        encryptor: Box<dyn Encryptor>,
        attestation_state: AttestationState,
        handshake_state: HandshakeState,
    },
    Error {
        attestation_state: Option<AttestationState>,
        handshake_state: Option<HandshakeState>,
    },
    /// A temporary state indicating that the session is currently transitioning
    /// between valid steps. Operations on a session in this state will fail.
    Invalid,
}

impl<AP: AttestationHandler, H: HandshakeHandler> Step<AP, H> {
    /// Transitions the session to the next logical step in the protocol.
    ///
    /// - From `Attestation` to `Handshake`: Occurs after
    ///   `attester.take_attestation_state()` is successful. The
    ///   `HandshakeHandler` is built using `handshake_handler_provider`.
    /// - From `Handshake` to `Open`: Occurs after `handshaker.take_crypter()`
    ///   is successful. The `Encryptor` is built using `encryptor_provider`.
    ///
    /// This method manages the ownership transfer of data (like
    /// `AttestationResults` to `Handshake` step, and `OrderedCrypter` to the
    /// `Encryptor`). If a transition fails (e.g., attestation failed, or
    /// provider fails to build), an error is returned, and the session
    /// typically remains in `Invalid` or the previous state if the
    /// transition was aborted early.
    fn next(&mut self) -> Result<(), Error> {
        // We can't transition between states without using this temp variable while
        // ensuring the memory safety because of the objects' lifetime.
        let old_state = mem::replace(self, Step::Invalid);
        match old_state {
            Step::Attestation {
                attester,
                handshake_handler_provider,
                encryptor_provider,
                attestation_publisher,
            } => {
                let attestation_state = match attester.take_attestation_state() {
                    core::result::Result::Ok(attestation_state) => attestation_state,
                    core::result::Result::Err(err) => {
                        *self = Step::Error { attestation_state: None, handshake_state: None };
                        return Err(err.context("retrieving attestation state failed"));
                    }
                };
                if let PeerAttestationVerdict::AttestationFailed { reason, .. } =
                    &attestation_state.peer_attestation_verdict
                {
                    if let Some(publisher) = attestation_publisher {
                        publisher.publish(AttestationEvidence::new_from_state(
                            &attestation_state,
                            &HandshakeState::default(),
                        ));
                    }
                    let attestation_failure_reason = reason.clone();
                    *self = Step::Error {
                        attestation_state: Some(attestation_state),
                        handshake_state: None,
                    };
                    return Err(anyhow!("attestation failed: {:?}", attestation_failure_reason));
                }

                // The peer bindings are expected whenever the peer provides evidence that can
                // be bound to the session. Even if the evidence hasn't been verified the peer
                // is expected (and required) to send the bindings for the evidence that it
                // supplies.
                let expect_peer_bindings =
                    attestation_state.peer_attestation_verdict.needs_session_bindings();
                let handshaker = match handshake_handler_provider
                    .build(expect_peer_bindings, attestation_state)
                {
                    core::result::Result::Ok(handshaker) => handshaker,
                    core::result::Result::Err(err) => {
                        *self = Step::Error { attestation_state: None, handshake_state: None };
                        return Err(err);
                    }
                };
                *self = Step::Handshake { encryptor_provider, attestation_publisher, handshaker };
            }
            Step::Handshake { handshaker, encryptor_provider, attestation_publisher } => {
                let (handshake_result, attestation_state) = match handshaker.take_handshake_result()
                {
                    core::result::Result::Ok((handshake_result, attestation_state)) => {
                        (handshake_result, attestation_state)
                    }
                    core::result::Result::Err(err) => {
                        *self = Step::Error { attestation_state: None, handshake_state: None };
                        return Err(err);
                    }
                };
                if let Err(err) = verify_session_binding(
                    &attestation_state.peer_session_binding_verifiers,
                    &handshake_result.handshake_state.peer_session_bindings,
                    handshake_result.handshake_state.handshake_binding_token.as_slice(),
                ) {
                    if let Some(publisher) = attestation_publisher {
                        publisher.publish(AttestationEvidence::new_from_state(
                            &attestation_state,
                            &handshake_result.handshake_state,
                        ));
                    }
                    *self = Step::Error {
                        attestation_state: Some(attestation_state),
                        handshake_state: Some(handshake_result.handshake_state),
                    };
                    return Err(err);
                }
                if let Err(err) = verify_assertion_session_binding(
                    attestation_state.peer_attestation_verdict.get_assertion_verification_results(),
                    &handshake_result.handshake_state.peer_assertion_bindings,
                    attestation_state.attestation_binding_token.as_slice(),
                    handshake_result.handshake_state.handshake_binding_token.as_slice(),
                ) {
                    if let Some(publisher) = attestation_publisher {
                        publisher.publish(AttestationEvidence::new_from_state(
                            &attestation_state,
                            &handshake_result.handshake_state,
                        ));
                    }
                    *self = Step::Error {
                        attestation_state: Some(attestation_state),
                        handshake_state: Some(handshake_result.handshake_state),
                    };
                    return Err(err);
                }
                if let Some(publisher) = attestation_publisher {
                    publisher.publish(AttestationEvidence::new_from_state(
                        &attestation_state,
                        &handshake_result.handshake_state,
                    ));
                }
                *self = Step::Open {
                    encryptor: encryptor_provider.provide_encryptor(handshake_result.crypter)?,
                    attestation_state,
                    handshake_state: handshake_result.handshake_state,
                };
            }
            Step::Open { .. } => {
                return Err(anyhow!("there is no next step when the session is open"))
            }
            Step::Invalid => return Err(anyhow!("session is currently in an invalid state")),
            Step::Error { .. } => return Err(anyhow!("session initialization already failed")),
        };
        Ok(())
    }

    /// Retrieves a `SessionBindingToken` if the session is in the `Open` state.
    ///
    /// Delegates to `SessionBindingToken::new` using the stored
    /// `handshake_binding_token`. Returns an error if the session is not yet
    /// open.
    fn get_session_binding_token(&self, info: &[u8]) -> Result<SessionBindingToken, Error> {
        match &self {
            Step::Open { handshake_state, .. } => {
                Ok(SessionBindingToken::new(&handshake_state.handshake_binding_token, info))
            }
            _ => Err(anyhow!("the session is not open")),
        }
    }

    /// Returns the attestation results for this session.
    ///
    /// This method can only be called successfully when `is_open()` is true.
    fn get_peer_attestation_evidence(&self) -> Result<AttestationEvidence, Error> {
        match &self {
            Step::Open { attestation_state, handshake_state, .. } => {
                Ok(AttestationEvidence::new_from_state(attestation_state, handshake_state))
            }
            Step::Error { attestation_state, handshake_state } => {
                Ok(AttestationEvidence::new_from_state(
                    attestation_state.as_ref().ok_or(anyhow!(
                        "session initialization failed, and no attestation evidence is available"
                    ))?,
                    handshake_state.as_ref().unwrap_or(&HandshakeState::default()),
                ))
            }
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
                attestation_publisher: config.attestation_publisher,
                handshake_handler_provider: Box::new(ClientHandshakeHandlerBuilder {
                    config: config.handshake_handler_config,
                }),
                encryptor_provider: config.encryptor_config.encryptor_provider,
            },
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
                    .context("encrypting plaintext")?;
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
                            .context("decrypting plaintext")?,
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

    /// Gets the peer attestation evidence. See
    /// `Session::get_peer_attestation_evidence`.
    fn get_peer_attestation_evidence(&self) -> Result<AttestationEvidence, Error> {
        self.step.get_peer_attestation_evidence()
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
            Step::Invalid | Step::Error { .. } => {
                return Err(anyhow!("session is in an invalid state"))
            }
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
    ///   Verifies server's session bindings using the
    ///   `SessionBindingVerifierProvider` from the configured
    ///   `PeerAttestationVerifier` and `attestation_results`. If handshake
    ///   completes, transitions to `Open`.
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
                Step::Handshake { handshaker, .. },
            ) => {
                handshaker.put_incoming_message(handshake_message)?.ok_or(anyhow!(
                    "invalid session state: handshake message received but handshaker doesn't
                     expect any"
                ))?;
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
                attestation_publisher: config.attestation_publisher,
                handshake_handler_provider: Box::new(ServerHandshakeHandlerBuilder {
                    config: config.handshake_handler_config,
                }),
                encryptor_provider: config.encryptor_config.encryptor_provider,
            },
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
                    .context("encrypting plaintext")?;
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
                            .context("decrypting plaintext")?,
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

    /// Gets the peer attestation evidence. See
    /// `Session::get_peer_attestation_evidence`.
    fn get_peer_attestation_evidence(&self) -> Result<AttestationEvidence, Error> {
        self.step.get_peer_attestation_evidence()
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
            Step::Invalid | Step::Error { .. } => Err(anyhow!("session is in an invalid state")),
        }
    }

    /// Processes an incoming `SessionRequest` from the client.
    ///
    /// Depending on the current `step` and message type:
    /// - `Attestation` + `AttestRequest`: Passes to `ServerAttestationHandler`.
    /// - `Handshake` + `HandshakeRequest`: Passes to `ServerHandshakeHandler`.
    ///   If this is the client's binding follow-up, verifies it using the
    ///   `SessionBindingVerifierProvider` from the configured
    ///   `PeerAttestationVerifier` and `attestation_results`. If handshake
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
                Step::Handshake { handshaker, .. },
            ) => {
                handshaker.put_incoming_message(handshake_message)?.ok_or(anyhow!(
                    "invalid session state: handshake message received but handshaker doesn't
                     expect any"
                ))?;
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
/// 1. Retrieves the corresponding `SessionBindingVerifier` from the
///    `binding_verifiers` map.
/// 2. Retrieves the corresponding `SessionBinding` from the `bindings` map.
/// 3. Calls `verify_binding` on the verifier with the `handshake_binding_token`
///    and the received binding.
///
/// This ensures that for each attested identity (via `attestation_results`),
/// its purported binding to the current session (via `handshake_binding_token`)
/// is cryptographically valid. An error is returned if any verification fails,
/// or if providers/bindings are missing.
fn verify_session_binding(
    binding_verifiers: &BTreeMap<String, Box<dyn SessionBindingVerifier>>,
    bindings: &BTreeMap<String, SessionBinding>,
    handshake_binding_token: &[u8],
) -> Result<(), Error> {
    for (id, binding_verifier) in binding_verifiers {
        binding_verifier.verify_binding(
            handshake_binding_token,
            bindings
                .get(id)
                .ok_or(anyhow!("peer hasn't sent a session binding for ID {id}"))?
                .binding
                .as_slice(),
        )?;
    }
    Ok(())
}

/// Verifies the received session `assertion_bindings` against the provided
/// `verified_bound_assertions`.
///
/// For each `VerifiedBoundAssertion` in `verified_bound_assertions`, this
/// function:
/// 1. Retrieves the corresponding `SessionBinding` from the
///    `assertion_bindings` map.
/// 2. Calls `verify_binding` on the assertion with the session binding token
///    derived from the handshake and all supplied and presented attestation
///    evidence.
///
/// This ensures that for each attested identity, its purported binding to the
/// current session and all the evidence exchanged during its initialization
/// (via `attestation_binding_token` and `handshake_hash`) is cryptographically
/// valid. An error is returned if any verification fails, or if
/// providers/bindings are missing.
fn verify_assertion_session_binding(
    verified_bound_assertions: &BTreeMap<String, BoundAssertionVerifierResult>,
    assertion_bindings: &BTreeMap<String, SessionBinding>,
    attestation_binding_token: &[u8],
    handshake_hash: &[u8],
) -> Result<(), Error> {
    let assertion_bound_data =
        create_session_binding_token(attestation_binding_token, handshake_hash);
    for (id, result) in verified_bound_assertions {
        if let BoundAssertionVerifierResult::Success { verified_bound_assertion: assertion } =
            result
        {
            let binding = assertion_bindings
                .get(id)
                .ok_or(anyhow!("peer hasn't sent an assertion binding for ID {id}"))?;
            assertion
                .verify_binding(assertion_bound_data.as_slice(), binding)
                .context("couldn't verify the assertion binding for ID {id}")?;
        }
    }
    Ok(())
}

impl AttestationEvidence {
    fn new_from_state(
        attestation_state: &AttestationState,
        handshake_state: &HandshakeState,
    ) -> Self {
        Self {
            evidence: attestation_state
                .peer_attestation_verdict
                .get_legacy_verification_results()
                .iter()
                .filter_map(|(id, verifier_result)| match verifier_result {
                    VerifierResult::Success { evidence, .. }
                    | VerifierResult::Failure { evidence, .. }
                    | VerifierResult::Unverified { evidence } => {
                        Some((id.clone(), evidence.clone()))
                    }
                    _ => None,
                })
                .collect(),
            evidence_bindings: handshake_state.peer_session_bindings.clone(),
            assertions: attestation_state
                .peer_attestation_verdict
                .get_assertion_verification_results()
                .iter()
                .filter_map(|(id, verifier_result)| match verifier_result {
                    BoundAssertionVerifierResult::Success { verified_bound_assertion, .. } => {
                        Some((id.clone(), verified_bound_assertion.assertion().clone()))
                    }
                    BoundAssertionVerifierResult::Failure { assertion, .. }
                    | BoundAssertionVerifierResult::Unverified { assertion } => {
                        Some((id.clone(), assertion.clone()))
                    }
                    _ => None,
                })
                .collect(),
            assertion_bindings: handshake_state.peer_assertion_bindings.clone(),
            handshake_hash: handshake_state.handshake_binding_token.clone(),
        }
    }
}
