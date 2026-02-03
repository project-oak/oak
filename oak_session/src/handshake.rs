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

//! This module provides implementations of the `HandshakeHandler` trait, which
//! handles the cryptographic handshake phase of establishing a secure session.
//! It primarily utilizes the Noise Protocol Framework to agree upon shared
//! session keys and a verifiable handshake transcript.
//!
//! ## Overview
//!
//! The handshake is a critical step in the overall session establishment
//! process, occurring after initial attestation (if any) and before secure
//! application data exchange. Its main responsibilities are:
//! - **Key Agreement**: Securely derive shared symmetric keys (returned as
//!   `OrderedCrypter`) that will be used to encrypt and decrypt messages
//!   exchanged during the session.
//! - **Transcript Hashing**: Produce a cryptographic hash (`handshake_hash`) of
//!   all messages exchanged during the handshake. This hash serves as a unique
//!   identifier for the handshake and is crucial for cryptographically binding
//!   the attestation results to this specific communication instance.
//! - **Authentication (Implicit/Explicit)**: Depending on the chosen
//!   `HandshakeType` (e.g., Noise KK, NK, NN patterns), parties may
//!   authenticate each other using pre-shared static public keys or rely on
//!   ephemeral key exchanges.
//!
//! ## Key Abstractions
//!
//! - **`HandshakeType`**: An enum specifying the desired Noise Protocol
//!   Framework pattern (e.g., `NoiseKK`, `NoiseNK`, `NoiseNN`). The choice of
//!   pattern determines how parties are authenticated and how keys are
//!   exchanged.
//! - **`HandshakeResult`**: A structure containing the outcomes of a successful
//!   handshake:
//!     - `session_keys`: The derived symmetric keys for encrypting session
//!       data.
//!     - `handshake_hash`: The hash of the handshake transcript, used for
//!       binding.
//!     - `peer_session_bindings`: Bindings (e.g., signatures) received from the
//!       peer, linking their attestation to this handshake.
//! - **`HandshakeHandler` Trait**: Defines the core interface for performing a
//!   handshake. It includes methods for obtaining the derived `session_keys`
//!   and `handshake_hash`, and checking if the handshake is complete. It also
//!   leverages the `ProtocolEngine` trait for sending and receiving handshake
//!   messages.
//! - **`ClientHandshakeHandler` and `ServerHandshakeHandler`**: Concrete
//!   implementations of the `HandshakeHandler` trait for the client (initiator)
//!   and server (responder) roles, respectively. They manage the state machine
//!   specific to their role in the chosen Noise protocol.
//! - **`HandshakeHandlerBuilder` Trait (and its implementations
//!   `ClientHandshakeHandlerBuilder`, `ServerHandshakeHandlerBuilder`)**: These
//!   act as factories for creating `HandshakeHandler` instances. This pattern
//!   is used by the main `Session` logic to construct the appropriate
//!   handshaker after the attestation phase, passing in necessary configuration
//!   (like identity keys and chosen `HandshakeType`).
//!
//! ## Interaction and Flow
//!
//! 1. A `HandshakeHandlerBuilder` is used to create either a
//!    `ClientHandshakeHandler` or a `ServerHandshakeHandler`, configured with
//!    cryptographic keys (via `IdentityKeyHandle`), the desired
//!    `HandshakeType`, and potentially `SessionBinder`s if the local party
//!    needs to send a session binding.
//! 2. The `Session` logic uses the `ProtocolEngine` methods on the
//!    `HandshakeHandler` (`get_outgoing_message`, `put_incoming_message`) to
//!    exchange one or more `HandshakeRequest` and `HandshakeResponse` messages
//!    with the peer.
//! 3. Internally, the `HandshakeHandler` uses the `oak_crypto::noise_handshake`
//!    primitives to process these messages according to the selected Noise
//!    pattern.
//! 4. Upon successful completion, the `HandshakeHandler` makes the
//!    `HandshakeResult` available, allowing the `Session` to retrieve the
//!    `session_keys` for creating an `Encryptor` and the `handshake_hash` for
//!    verifying session bindings.

use alloc::{boxed::Box, collections::BTreeMap, string::String, sync::Arc, vec::Vec};
use core::convert::TryInto;

use anyhow::{Context, Error, anyhow};
use oak_crypto::{
    identity_key::IdentityKeyHandle,
    noise_handshake::{
        OrderedCrypter, Response, client::HandshakeInitiator, respond_kk, respond_nk, respond_nn,
    },
};
use oak_proto_rust::oak::session::v1::{
    HandshakeRequest, HandshakeResponse, NoiseHandshakeMessage, SessionBinding, handshake_request,
    handshake_response,
};

use crate::{
    ProtocolEngine,
    attestation::AttestationState,
    config::HandshakeHandlerConfig,
    session_binding::{SessionBinder, create_session_binding_token},
};

/// Specifies the type of Noise Protocol Framework handshake pattern to be used.
///
/// Each variant corresponds to a specific Noise pattern (e.g., KK, NK, NN),
/// determining how parties authenticate and exchange keys.
#[derive(Copy, Clone, Debug)]
pub enum HandshakeType {
    NoiseKK,
    NoiseKN,
    NoiseNK,
    NoiseNN,
}

/// Holds the results of a successfully completed Oak Session handshake.
///
/// This structure encapsulates the essential cryptographic material derived
/// from the handshake, which is then used to secure the communication channel
/// and potentially bind the session to the attestation phase.
pub struct HandshakeResult {
    /// Crypter using the symmetric keys (e.g., encryption/decryption keys)
    /// established during the handshake. The crypter id used by an
    /// `Encryptor` to protect application messages.
    pub crypter: OrderedCrypter,
    /// The state of the completed handshake, including the handshake hash and
    /// any peer bindings.
    pub handshake_state: HandshakeState,
}

/// Contains the state of a completed handshake.
#[derive(Default)]
pub struct HandshakeState {
    /// A cryptographic hash of the entire transcript of messages exchanged
    /// during the handshake. This hash is crucial for binding the
    /// attestation results to the handshake, ensuring that the attested
    /// peer is the one participating in this specific handshake.
    pub handshake_binding_token: Vec<u8>,
    /// Session bindings received from the peer. These are typically signatures
    /// or MACs over the session binding token (or related data), created using
    /// keys derived from the peer's attestation. Verifying these bindings
    /// confirms the link between the attested identity and the current
    /// session.
    pub peer_session_bindings: BTreeMap<String, SessionBinding>,
    /// Bindings for assertions received from the peer.
    pub peer_assertion_bindings: BTreeMap<String, SessionBinding>,
}

/// A trait for building a `HandshakeHandler` instance.
///
/// This factory trait allows for deferred creation of a `HandshakeHandler`,
/// encapsulating the necessary configuration. This is useful in the `Session`
/// state machine where the `HandshakeHandler` is created after the attestation
/// phase.
pub trait HandshakeHandlerBuilder<T: HandshakeHandler>: Send {
    /// Builds and returns a `HandshakeHandler` instance.
    ///
    /// Arguments:
    ///
    /// * `expect_peer_bindings`: Specifies if the peer is expected to send
    ///   session bindings at the end of the handshake (true if the peer is
    ///   attested)
    ///
    /// The lifetime of the returned `HandshakeHandler` is owned by the caller.
    /// Configuration data is typically moved into the builder and then into the
    /// `HandshakeHandler`.
    fn build(
        self: Box<Self>,
        expect_peer_bindings: bool,
        attestation_state: AttestationState,
    ) -> Result<T, Error>;
}

/// A builder for creating `ClientHandshakeHandler` instances.
///
/// It holds the `HandshakeHandlerConfig` required to initialize the client-side
/// handshake.
pub struct ClientHandshakeHandlerBuilder {
    pub config: HandshakeHandlerConfig,
}

impl HandshakeHandlerBuilder<ClientHandshakeHandler> for ClientHandshakeHandlerBuilder {
    /// Constructs a `ClientHandshakeHandler` using the stored configuration.
    fn build(
        self: Box<Self>,
        _expect_peer_bindings: bool,
        attestation_state: AttestationState,
    ) -> Result<ClientHandshakeHandler, Error> {
        ClientHandshakeHandler::create(self.config, attestation_state)
    }
}

/// A builder for creating `ServerHandshakeHandler` instances.
///
/// It holds the `HandshakeHandlerConfig` and a flag indicating whether to
/// expect a session binding message from the client.
pub struct ServerHandshakeHandlerBuilder {
    pub config: HandshakeHandlerConfig,
}

impl HandshakeHandlerBuilder<ServerHandshakeHandler> for ServerHandshakeHandlerBuilder {
    /// Constructs a `ServerHandshakeHandler` using the stored configuration.
    fn build(
        self: Box<Self>,
        expect_peer_bindings: bool,
        attestation_state: AttestationState,
    ) -> Result<ServerHandshakeHandler, Error> {
        Ok(ServerHandshakeHandler::new(self.config, expect_peer_bindings, attestation_state))
    }
}

/// Defines the contract for a cryptographic handshaker.
///
/// A `HandshakeHandler` is responsible for executing a Noise protocol handshake
/// to establish shared session keys and a handshake hash. Implementations are
/// stateful and use the `ProtocolEngine` trait to exchange handshake messages.
pub trait HandshakeHandler: Send {
    /// Retrieves the result of the completed handshake including the derived
    /// crypter. Also passes along the attestation state so that it could be
    /// used later in the session.
    ///
    /// This method consumes aelf, meaning it can only be
    /// called once. It returns an error if the handshake is
    /// not yet complete keys are not ready. Can only be called once.
    fn take_handshake_result(self) -> Result<(HandshakeResult, AttestationState), Error>;

    /// Checks if the handshake process is fully complete.
    ///
    /// A handshake is complete when all necessary messages have been exchanged
    /// and processed, and session keys and the handshake hash are
    /// available. For some protocols (e.g., client-attested scenarios),
    /// this might include waiting for a final follow-up message from the
    /// client containing its session binding.
    fn is_handshake_complete(&self) -> bool;
}

/// Client-side implementation of the `HandshakeHandler`.
///
/// Manages the state for the client (initiator) during a Noise handshake.
/// It constructs the initial handshake message and processes the server's
/// response. If client attestation is involved (`session_binders` is not
/// empty), it may also prepare a follow-up message containing the client's
/// session binding.
pub struct ClientHandshakeHandler {
    /// The `HandshakeInitiator` is used to generate the initial handshake
    /// message and process the server's response.
    handshake_initiator: HandshakeInitiator,
    /// The `session_binders` are used to generate the follow-up message
    /// containing the client's session binding.
    session_binders: BTreeMap<String, Arc<dyn SessionBinder>>,
    /// The state from the preceding attestation phase, which is carried through
    /// the handshake and used for binding attestation information to the
    /// session.
    attestation_state: AttestationState,
    /// The initial handshake message sent to the server.
    initial_message: Option<HandshakeRequest>,
    /// The follow-up handshake message sent to the server.
    followup_message: Option<HandshakeRequest>,
    /// The result of the completed handshake, containing the session keys and
    /// handshake hash.
    handshake_result: Option<HandshakeResult>,
}

impl ClientHandshakeHandler {
    /// Creates a new `ClientHandshakeHandler` and prepares the initial
    /// handshake message.
    ///
    /// Initializes the Noise protocol state based on
    /// `handshake_handler_config.handshake_type` and any provided static keys.
    /// The first message to be sent to the server is generated and stored
    /// internally, ready to be retrieved by `get_outgoing_message`.
    ///
    /// The `handshake_handler_config` is consumed, and its owned data (like
    /// keys) is moved into the `ClientHandshakeHandler`.
    pub fn create(
        handshake_handler_config: HandshakeHandlerConfig,
        attestation_state: AttestationState,
    ) -> anyhow::Result<Self> {
        let handshake_type = handshake_handler_config.handshake_type;
        let peer_static_public_key = handshake_handler_config.peer_static_public_key.clone();
        let mut handshake_initiator = match handshake_type {
            HandshakeType::NoiseKN => core::unimplemented!(),
            HandshakeType::NoiseKK => HandshakeInitiator::new_kk(
                peer_static_public_key
                    .context("no peer_static_public_key in handshake_handler_config")?
                    .as_slice()
                    .try_into()
                    .map_err(|error| anyhow!("invalid peer public key: {:?}", error))?,
                handshake_handler_config
                    .self_static_private_key
                    .context("no self_static_private_key in handshake_handler_config")?,
            ),
            HandshakeType::NoiseNK => HandshakeInitiator::new_nk(
                peer_static_public_key
                    .context("no peer_static_public_key in handshake_handler_config")?
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
            ..Default::default()
        };
        Ok(Self {
            handshake_initiator,
            session_binders: handshake_handler_config.session_binders,
            attestation_state,
            initial_message: Some(initial_message),
            followup_message: None,
            handshake_result: None,
        })
    }
}

impl HandshakeHandler for ClientHandshakeHandler {
    /// Retrieves the handshake result. See
    /// `HandshakeHandler::take_handshake_result`.
    fn take_handshake_result(mut self) -> Result<(HandshakeResult, AttestationState), Error> {
        Ok((
            self.handshake_result.take().ok_or(anyhow!("handshake is not complete"))?,
            self.attestation_state,
        ))
    }

    /// Checks if the client's handshake is complete.
    /// This includes sending any follow-up binding message if client
    /// attestation is used.
    fn is_handshake_complete(&self) -> bool {
        self.handshake_result.is_some() && self.followup_message.is_none()
    }
}

/// Implements the `ProtocolEngine` for the `ClientHandshakeHandler`, defining
/// how it exchanges messages with the server during the handshake.
impl ProtocolEngine<HandshakeResponse, HandshakeRequest> for ClientHandshakeHandler {
    /// Retrieves the next outgoing `HandshakeRequest` to be sent to the server.
    ///
    /// This method is called by the session logic to get the client's messages.
    /// - Initially, it returns the first handshake message (e.g., client's
    ///   ephemeral public key and potentially its static key, depending on the
    ///   Noise pattern).
    /// - If client attestation is configured (i.e., `session_binders` is not
    ///   empty), after processing the server's response, this method will
    ///   return a second `HandshakeRequest` containing the client's
    ///   `SessionBinding`s.
    /// - Returns `Ok(None)` when there are no more messages to send from the
    ///   client side.
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<HandshakeRequest>> {
        if let Some(initial_message) = self.initial_message.take() {
            Ok(Some(initial_message))
        } else {
            Ok(self.followup_message.take())
        }
    }

    /// Processes an incoming `HandshakeResponse` from the server.
    ///
    /// This method is called by the session logic when a message from the
    /// server is received.
    /// - It uses the `HandshakeInitiator` to process the server's Noise
    ///   protocol message.
    /// - On successful processing, it extracts the `OrderedCrypter`,
    ///   `handshake_binding_token`, and any `peer_session_bindings` sent by the
    ///   server, storing them in `handshake_result`.
    /// - If client `session_binders` are configured, this method prepares the
    ///   `followup_message` with the client's own bindings, which will be sent
    ///   via a subsequent call to `get_outgoing_message`.
    /// - Returns `Ok(Some(()))` if the message was processed successfully.
    /// - Returns `Ok(None)` if the handshake is already complete and no further
    ///   messages are expected.
    /// - Returns an `Err` if message processing fails (e.g., cryptographic
    ///   verification error).
    fn put_incoming_message(
        &mut self,
        incoming_message: HandshakeResponse,
    ) -> anyhow::Result<Option<()>> {
        if self.handshake_result.is_some() {
            // The handshake result is ready - no other messages expected.
            return Ok(None);
        }
        match incoming_message.r#handshake_type {
            Some(handshake_response::HandshakeType::NoiseHandshakeMessage(noise_message)) => {
                let handshake_result = self
                    .handshake_initiator
                    .process_response(&noise_message.into())
                    .map_err(|e| anyhow!("Error processing response: {e:?}"))
                    .map(|(handshake_hash, crypter)| HandshakeResult {
                        crypter,
                        handshake_state: HandshakeState {
                            handshake_binding_token: handshake_hash.to_vec(),
                            peer_session_bindings: incoming_message.attestation_bindings,
                            peer_assertion_bindings: incoming_message.assertion_bindings,
                        },
                    })?;
                if !self.session_binders.is_empty()
                    || !self.attestation_state.self_assertions.is_empty()
                {
                    let assertion_bound_data = create_session_binding_token(
                        self.attestation_state.attestation_binding_token.as_slice(),
                        handshake_result.handshake_state.handshake_binding_token.as_slice(),
                    );
                    self.followup_message = Some(HandshakeRequest {
                        r#handshake_type: None,
                        attestation_bindings: self
                            .session_binders
                            .iter()
                            .map(|(id, binder)| {
                                (
                                    id.clone(),
                                    SessionBinding {
                                        binding: binder.bind(
                                            handshake_result
                                                .handshake_state
                                                .handshake_binding_token
                                                .as_slice(),
                                        ),
                                    },
                                )
                            })
                            .collect(),
                        assertion_bindings: self
                            .attestation_state
                            .self_assertions
                            .iter()
                            .map(|(id, assertion)| {
                                Ok((id.clone(), assertion.bind(assertion_bound_data.as_slice())?))
                            })
                            .collect::<Result<BTreeMap<String, SessionBinding>, Error>>()?,
                    });
                }

                self.handshake_result = Some(handshake_result);
                Ok(Some(()))
            }
            None => Err(anyhow!("Missing handshake_type")),
        }
    }
}

/// Server-side implementation of the `HandshakeHandler`.
///
/// Manages the state for the server (responder) during a Noise handshake.
/// It processes the client's initial handshake message and generates a
/// response. If server attestation is involved (`session_binders` is not
/// empty), its response will include the server's session binding. It may also
/// expect a follow-up message from the client if `client_binding_expected` is
/// true.
#[allow(dead_code)]
pub struct ServerHandshakeHandler {
    /// The type of Noise handshake to perform.
    handshake_type: HandshakeType,
    /// The server's static private key.
    self_identity_key: Option<Box<dyn IdentityKeyHandle>>,
    /// The peer's static public key, if required by the handshake type.
    peer_public_key: Option<Vec<u8>>,
    /// Binders used to generate session bindings from the server's attestation.
    session_binders: BTreeMap<String, Arc<dyn SessionBinder>>,
    /// Whether to expect a follow-up message with the client's session
    /// bindings.
    client_binding_expected: bool,
    /// The state from the preceding attestation phase, which is carried through
    /// the handshake and used for binding attestation information to the
    /// session.
    attestation_state: AttestationState,
    /// The Noise protocol response, kept temporarily if a follow-up message is
    /// expected from the client.
    noise_response: Option<Response>,
    /// The generated handshake response to be sent to the client.
    handshake_response: Option<HandshakeResponse>,
    /// The result of a successfully completed handshake.
    handshake_result: Option<HandshakeResult>,
}

impl ServerHandshakeHandler {
    /// Creates a new `ServerHandshakeHandler`.
    ///
    /// `handshake_handler_config` provides the necessary cryptographic keys and
    /// handshake type. `client_binding_expected` informs the server whether
    /// to wait for a follow-up message from the client containing the
    /// client's session binding after the main handshake response has been
    /// sent.
    ///
    /// The `handshake_handler_config` is consumed.
    pub fn new(
        handshake_handler_config: HandshakeHandlerConfig,
        client_binding_expected: bool,
        attestation_state: AttestationState,
    ) -> Self {
        Self {
            handshake_type: handshake_handler_config.handshake_type,
            self_identity_key: handshake_handler_config.self_static_private_key,
            peer_public_key: handshake_handler_config.peer_static_public_key,
            session_binders: handshake_handler_config.session_binders,
            client_binding_expected,
            attestation_state,
            noise_response: None,
            handshake_response: None,
            handshake_result: None,
        }
    }
}

impl HandshakeHandler for ServerHandshakeHandler {
    /// Retrieves the handshake result. See
    /// `HandshakeHandler::take_handshake_result`.
    fn take_handshake_result(mut self) -> Result<(HandshakeResult, AttestationState), Error> {
        Ok((
            self.handshake_result.take().ok_or(anyhow!("handshake is not complete"))?,
            self.attestation_state,
        ))
    }

    /// Checks if the server's handshake is complete.
    /// This depends on whether a client binding follow-up message is expected.
    fn is_handshake_complete(&self) -> bool {
        self.handshake_result.is_some()
    }
}

impl ProtocolEngine<HandshakeRequest, HandshakeResponse> for ServerHandshakeHandler {
    /// Gets the outgoing `HandshakeResponse` to be sent to the client.
    ///
    /// This message is generated after processing the client's initial
    /// `HandshakeRequest`. It will contain the server's contribution to the
    /// Noise handshake and, if server `session_binders` are configured, the
    /// server's session binding. This method typically returns
    /// `Some(HandshakeResponse)` once.
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<HandshakeResponse>> {
        Ok(self.handshake_response.take())
    }

    /// Processes an incoming `HandshakeRequest` from the client.
    ///
    /// If this is the initial request from the client, it advances the Noise
    /// protocol, generates a `HandshakeResponse` (stored for
    /// `get_outgoing_message`), and derives `session_keys` and
    /// `handshake_hash`. If server `session_binders` are configured,
    /// the binding is included in the response.
    ///
    /// If `client_binding_expected` is true, this method may be called again to
    /// process the client's follow-up binding message, at which point the
    /// client's `peer_session_bindings` are stored.
    fn put_incoming_message(
        &mut self,
        incoming_message: HandshakeRequest,
    ) -> anyhow::Result<Option<()>> {
        if self.handshake_result.is_some() {
            // The handshake result is ready - no other messages expected.
            return Ok(None);
        }
        if let Some(noise_response) = self.noise_response.take() {
            self.handshake_result = Some(HandshakeResult {
                crypter: noise_response.crypter,
                handshake_state: HandshakeState {
                    handshake_binding_token: noise_response.handshake_hash.to_vec(),
                    peer_session_bindings: incoming_message.attestation_bindings,
                    peer_assertion_bindings: incoming_message.assertion_bindings,
                },
            });
        } else {
            let noise_response = match incoming_message.r#handshake_type {
                Some(handshake_request::HandshakeType::NoiseHandshakeMessage(noise_message)) => {
                    match self.handshake_type {
                        HandshakeType::NoiseKN => core::unimplemented!(),
                        HandshakeType::NoiseKK => respond_kk(
                            self.self_identity_key
                                .as_ref()
                                .context("no self_identity_key in handshake_handler_config")?
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
                                .context("no self_identity_key in handshake_handler_config")?
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
            let assertion_bound_data = create_session_binding_token(
                self.attestation_state.attestation_binding_token.as_slice(),
                noise_response.handshake_hash.as_slice(),
            );
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
                        (
                            id.clone(),
                            SessionBinding {
                                binding: binder.bind(noise_response.handshake_hash.as_slice()),
                            },
                        )
                    })
                    .collect(),
                assertion_bindings: self
                    .attestation_state
                    .self_assertions
                    .iter()
                    .map(|(id, assertion)| {
                        Ok((id.clone(), assertion.bind(assertion_bound_data.as_slice())?))
                    })
                    .collect::<Result<BTreeMap<String, SessionBinding>, Error>>()?,
            });
            if self.client_binding_expected {
                self.noise_response = Some(noise_response);
            } else {
                self.handshake_result = Some(HandshakeResult {
                    crypter: noise_response.crypter,
                    handshake_state: HandshakeState {
                        handshake_binding_token: noise_response.handshake_hash.to_vec(),
                        peer_session_bindings: BTreeMap::new(),
                        peer_assertion_bindings: BTreeMap::new(),
                    },
                })
            }
        }
        Ok(Some(()))
    }
}
