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

//! This module defines the configuration structures and a builder pattern
//! (`SessionConfigBuilder`) used to set up and customize `Session` instances.
//! It centralizes all the necessary settings for the various phases of a secure
//! session, including:
//!
//! - **Attestation**: Specifies the type of attestation to perform (e.g.,
//!   bidirectional, unidirectional), which attesters and endorsers to use for
//!   self-attestation, and which verifiers to use for peer attestation.
//!   Configuration is held in [`AttestationHandlerConfig`].
//! - **Handshake**: Defines the cryptographic handshake protocol (e.g., Noise
//!   patterns like KK, NK, NN), and any pre-shared static keys required by the
//!   chosen protocol. Configuration is held in [`HandshakeHandlerConfig`].
//! - **Encryption**: Determines how session encryptors are provided after a
//!   successful handshake. Configuration is held in [`EncryptorConfig`].
//! - **Session Binding**: Manages how attestation results are cryptographically
//!   bound to the session. This includes providers for verifying session
//!   bindings received from the peer, and binders for this party to create its
//!   own session bindings.
//!
//! The [`SessionConfig`] struct is the main container for all these settings,
//! and the [`SessionConfigBuilder`] provides a fluent API to construct it
//! step-by-step. This approach allows for flexible and clear configuration of
//! complex session establishment logic.

use alloc::{boxed::Box, collections::BTreeMap, string::String, sync::Arc, vec::Vec};

use anyhow::Error;
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_crypto::{
    encryptor::Encryptor, identity_key::IdentityKeyHandle, noise_handshake::OrderedCrypter,
};

use crate::{
    aggregators::{
        AssertionResultsAggregator, DefaultLegacyVerifierResultsAggregator, Empty,
        LegacyVerifierResultsAggregator,
    },
    attestation::AttestationType,
    encryptors::OrderedChannelEncryptor,
    generator::AssertionGenerator,
    handshake::HandshakeType,
    key_extractor::{DefaultSigningKeyExtractor, KeyExtractor},
    session::AttestationPublisher,
    session_binding::{
        SessionBinder, SessionBindingVerifierProvider, SignatureBindingVerifierProvider,
    },
    verifier::AssertionVerifier,
};

/// Top-level configuration for a secure session.
///
/// This struct aggregates configurations for attestation, handshake,
/// encryption, and session binding verification. Instances are typically
/// created using the [`SessionConfigBuilder`].
#[allow(dead_code)]
pub struct SessionConfig {
    /// Configuration for the attestation phase.
    pub attestation_type: AttestationType,
    /// Configuration for the attestation phase.
    pub attestation_handler_config: AttestationHandlerConfig,
    /// Configuration for the cryptographic handshake phase.
    pub handshake_handler_config: HandshakeHandlerConfig,
    /// Configuration for creating the session encryptor.
    pub encryptor_config: EncryptorConfig,
    /// An [`AttestationPublisher`] can optionally be provided. If it is, it
    /// will be called when the session receives an [`EndorsedEvidence`] from
    /// the peer, before verification occurs.
    pub attestation_publisher: Option<Arc<dyn AttestationPublisher>>,
}

impl SessionConfig {
    /// Creates a new [`SessionConfigBuilder`] to construct a `SessionConfig`.
    ///
    /// # Arguments
    ///
    /// * `attestation_type`: Specifies the attestation flow (e.g.,
    ///   bidirectional, unidirectional).
    /// * `handshake_type`: Specifies the cryptographic handshake protocol to
    ///   use.
    pub fn builder(
        attestation_type: AttestationType,
        handshake_type: HandshakeType,
    ) -> SessionConfigBuilder {
        SessionConfigBuilder::new(attestation_type, handshake_type)
    }
}

/// A builder for creating [`SessionConfig`] instances.
///
/// Provides a fluent API to configure all aspects of a secure session.
pub struct SessionConfigBuilder {
    config: SessionConfig,
}

/// Trait for objects that can provide an [`Encryptor`] instance.
///
/// This allows deferring the creation of the encryptor until session keys are
/// available after a successful handshake.
pub trait EncryptorProvider: Send {
    fn provide_encryptor(&self, crypter: OrderedCrypter) -> Result<Box<dyn Encryptor>, Error>;
}

/// An [`EncryptorProvider`] that creates [`OrderedChannelEncryptor`] instances.
pub struct OrderedChannelEncryptorProvider;

impl EncryptorProvider for OrderedChannelEncryptorProvider {
    fn provide_encryptor(&self, crypter: OrderedCrypter) -> Result<Box<dyn Encryptor>, Error> {
        TryInto::<OrderedChannelEncryptor>::try_into(crypter)
            .map(|v| Box::new(v) as Box<dyn Encryptor>)
    }
}

impl SessionConfigBuilder {
    /// Creates a new `SessionConfigBuilder` with essential attestation and
    /// handshake types.
    ///
    /// Initializes with default configurations for attestation (no attesters,
    /// endorsers, or verifiers), handshake (no static keys or session binders),
    /// and encryption (using `OrderedChannelEncryptorProvider`).
    fn new(attestation_type: AttestationType, handshake_type: HandshakeType) -> Self {
        let attestation_handler_config = AttestationHandlerConfig::default();

        let handshake_handler_config = HandshakeHandlerConfig {
            handshake_type,
            self_static_private_key: None,
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        };

        let encryptor_config =
            EncryptorConfig { encryptor_provider: Box::new(OrderedChannelEncryptorProvider) };

        let config = SessionConfig {
            attestation_type,
            attestation_handler_config,
            handshake_handler_config,
            encryptor_config,
            attestation_publisher: None,
        };
        Self { config }
    }

    /// Add an Attester that generates [`Evidence`] for this party (self).
    /// The `attestation_id` is a string identifier that is sent alongside the
    /// [`Evidence`]. The peer uses this ID to select the corresponding
    /// [`AttestationVerifier`] for verification.
    ///
    /// Reference: <https://datatracker.ietf.org/doc/html/rfc9334#name-attester>
    pub fn add_self_attester(mut self, attester_id: String, attester: Box<dyn Attester>) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::SelfUnidirectional
            ),
            "Self-attestation is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        self.config.attestation_handler_config.self_attesters.insert(attester_id, attester.into());
        self
    }

    /// Add an Attester by reference, retaining ownership of the attester
    /// object. See [`add_self_attester`] for more details on `attestation_id`.
    pub fn add_self_attester_ref(
        mut self,
        attester_id: String,
        attester: &Arc<dyn Attester>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::SelfUnidirectional
            ),
            "Self-attestation is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        self.config.attestation_handler_config.self_attesters.insert(attester_id, attester.clone());
        self
    }

    /// Add an Endorser that generates [`Endorsements`] for this party's (self)
    /// [`Evidence`]. The `endorser_id` must match the `attestation_id` of the
    /// [`Attester`] whose [`Evidence`] it is endorsing.
    ///
    /// Reference: <https://datatracker.ietf.org/doc/html/rfc9334#name-endorser-reference-value-pr>
    pub fn add_self_endorser(mut self, endorser_id: String, endorser: Box<dyn Endorser>) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::SelfUnidirectional
            ),
            "Self-endorsement is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        self.config.attestation_handler_config.self_endorsers.insert(endorser_id, endorser.into());
        self
    }

    /// Add an Endorser by reference, retaining ownership of the endorser
    /// object. See [`add_self_endorser`] for more details on `endorser_id`.
    pub fn add_self_endorser_ref(
        mut self,
        endorser_id: String,
        endorser: &Arc<dyn Endorser>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::SelfUnidirectional
            ),
            "Self-endorsement is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        self.config.attestation_handler_config.self_endorsers.insert(endorser_id, endorser.clone());
        self
    }

    /// Add an [`AssertionGenerator`] that generates an [`Assertion`] for this
    /// party (self). The `assertion_id` is a string identifier that is sent
    /// alongside the [`Assertion`]. The peer uses this ID to select the
    /// corresponding [`AssertionVerifier`] for verification.
    pub fn add_self_assertion_generator(
        mut self,
        assertion_id: String,
        generator: Box<dyn AssertionGenerator>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::SelfUnidirectional
            ),
            "Self-attestation is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        self.config
            .attestation_handler_config
            .self_assertion_generators
            .insert(assertion_id, generator.into());
        self
    }

    /// Add an [`AssertionGenerator`] by reference, retaining ownership of the
    /// generator object. See [`add_self_assertion_generator`] for more details
    /// on `assertion_id`.
    pub fn add_self_assertion_generator_ref(
        mut self,
        assertion_id: String,
        generator: &Arc<dyn AssertionGenerator>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::SelfUnidirectional
            ),
            "Self-attestation is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        self.config
            .attestation_handler_config
            .self_assertion_generators
            .insert(assertion_id, generator.clone());
        self
    }

    /// Add an [`AttestationPublisher`] for this configuration.
    ///
    /// Only one publisher can be set per configuration. If you called this
    /// function multiple times, only the most recent one will be added.
    pub fn add_attestation_publisher(mut self, publisher: &Arc<dyn AttestationPublisher>) -> Self {
        self.config.attestation_publisher = Some(publisher.clone());
        self
    }

    /// Add an [`AttestationVerifier`] to verify [`Evidence`] and
    /// [`Endorsements`] received from the peer. The `attestation_id` is used
    /// to match this verifier with the `attestation_id` accompanying the
    /// peer's [`Evidence`]. This method uses a default [`KeyExtractor`]
    /// ([`DefaultSigningKeyExtractor`]) to extract a key from the verified
    /// attestation results, which is then used to create a
    /// [`SessionBindingVerifierProvider`] for ensuring the peer's
    /// attestation is bound to the current session.
    ///
    /// Reference: <https://datatracker.ietf.org/doc/html/rfc9334#name-verifier>
    pub fn add_peer_verifier(
        mut self,
        attester_id: String,
        verifier: Box<dyn AttestationVerifier>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::PeerUnidirectional
            ),
            "Peer verification is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        let peer_verifier = PeerAttestationVerifier {
            verifier: verifier.into(),
            binding_verifier_provider: Arc::new(SignatureBindingVerifierProvider::new(Arc::new(
                DefaultSigningKeyExtractor {},
            ))),
        };
        self.config.attestation_handler_config.peer_verifiers.insert(attester_id, peer_verifier);
        self
    }

    /// Add an [`AttestationVerifier`] by reference, retaining ownership.
    /// See [`add_peer_verifier`] for details on `attestation_id` and default
    /// session binding verification.
    pub fn add_peer_verifier_ref(
        mut self,
        attester_id: String,
        verifier: &Arc<dyn AttestationVerifier>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::PeerUnidirectional
            ),
            "Peer verification is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        let peer_verifier = PeerAttestationVerifier {
            verifier: verifier.clone(),
            binding_verifier_provider: Arc::new(SignatureBindingVerifierProvider::new(Arc::new(
                DefaultSigningKeyExtractor {},
            ))),
        };
        self.config.attestation_handler_config.peer_verifiers.insert(attester_id, peer_verifier);
        self
    }

    /// Add an [`AttestationVerifier`] with a custom [`KeyExtractor`].
    /// The `attestation_id` matches the verifier to the peer's [`Evidence`].
    /// The provided `key_extractor` is used to derive a key from the peer's
    /// verified attestation results. This key is then used by a
    /// [`SignatureBindingVerifierProvider`] to verify that the peer's
    /// attestation is bound to the current session.
    ///
    /// Reference: <https://datatracker.ietf.org/doc/html/rfc9334#name-verifier>
    pub fn add_peer_verifier_with_key_extractor(
        mut self,
        attester_id: String,
        verifier: Box<dyn AttestationVerifier>,
        key_extractor: Box<dyn KeyExtractor>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::PeerUnidirectional
            ),
            "Peer verification is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        let peer_verifier = PeerAttestationVerifier {
            verifier: verifier.into(),
            binding_verifier_provider: Arc::new(SignatureBindingVerifierProvider::new(
                key_extractor.into(),
            )),
        };
        self.config.attestation_handler_config.peer_verifiers.insert(attester_id, peer_verifier);
        self
    }

    /// Add an [`AttestationVerifier`] and a custom [`KeyExtractor`] by
    /// reference. Retains ownership of the provided objects. See
    /// [`add_peer_verifier_with_key_extractor`] for more details.
    pub fn add_peer_verifier_with_key_extractor_ref(
        mut self,
        attester_id: String,
        verifier: &Arc<dyn AttestationVerifier>,
        key_extractor: &Arc<dyn KeyExtractor>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::PeerUnidirectional
            ),
            "Peer verification is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        let peer_verifier = PeerAttestationVerifier {
            verifier: verifier.clone(),
            binding_verifier_provider: Arc::new(SignatureBindingVerifierProvider::new(
                key_extractor.clone(),
            )),
        };
        self.config.attestation_handler_config.peer_verifiers.insert(attester_id, peer_verifier);
        self
    }

    /// Add an [`AttestationVerifier`] with a custom
    /// [`SessionBindingVerifierProvider`]. The `attestation_id` matches the
    /// verifier to the peer's [`Evidence`]. The `binding_verifier_provider`
    /// is directly used to create a verifier for the peer's session
    /// binding, offering maximum flexibility in how session binding is
    /// verified.
    ///
    /// Reference: <https://datatracker.ietf.org/doc/html/rfc9334#name-verifier>
    pub fn add_peer_verifier_with_binding_verifier_provider(
        mut self,
        attester_id: String,
        verifier: Box<dyn AttestationVerifier>,
        binding_verifier_provider: Box<dyn SessionBindingVerifierProvider>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::PeerUnidirectional
            ),
            "Peer verification is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        let peer_verifier = PeerAttestationVerifier {
            verifier: verifier.into(),
            binding_verifier_provider: binding_verifier_provider.into(),
        };
        self.config.attestation_handler_config.peer_verifiers.insert(attester_id, peer_verifier);
        self
    }

    /// Add an [`AttestationVerifier`] and a custom
    /// [`SessionBindingVerifierProvider`] by reference. Retains ownership
    /// of the provided objects. See
    /// [`add_peer_verifier_with_binding_verifier_provider`] for more details.
    pub fn add_peer_verifier_with_binding_verifier_provider_ref(
        mut self,
        attester_id: String,
        verifier: &Arc<dyn AttestationVerifier>,
        binding_verifier_provider: &Arc<dyn SessionBindingVerifierProvider>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::PeerUnidirectional
            ),
            "Peer verification is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        let peer_verifier = PeerAttestationVerifier {
            verifier: verifier.clone(),
            binding_verifier_provider: binding_verifier_provider.clone(),
        };
        self.config.attestation_handler_config.peer_verifiers.insert(attester_id, peer_verifier);
        self
    }

    pub fn add_peer_assertion_verifier(
        mut self,
        assertion_id: String,
        verifier: Box<dyn AssertionVerifier>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::PeerUnidirectional
            ),
            "Peer verification is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        self.config
            .attestation_handler_config
            .peer_assertion_verifiers
            .insert(assertion_id, verifier.into());
        self
    }

    pub fn add_peer_assertion_verifier_ref(
        mut self,
        assertion_id: String,
        verifier: &Arc<dyn AssertionVerifier>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::PeerUnidirectional
            ),
            "Peer verification is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        self.config
            .attestation_handler_config
            .peer_assertion_verifiers
            .insert(assertion_id, verifier.clone());
        self
    }

    /// Sets this party's static private key for the handshake.
    ///
    /// This key is used in handshake patterns that require the party to have a
    /// pre-known static identity (e.g., Noise patterns like IK, KK).
    /// Panics if the key has already been set.
    pub fn set_self_static_private_key(mut self, private_key: Box<dyn IdentityKeyHandle>) -> Self {
        if self.config.handshake_handler_config.self_static_private_key.is_none() {
            self.config.handshake_handler_config.self_static_private_key = Some(private_key);
        } else {
            panic!("self private key has already been set");
        }
        self
    }

    /// Sets the peer's static public key for the handshake.
    ///
    /// This key is used in handshake patterns where the peer's static identity
    /// is known beforehand (e.g., Noise patterns like IK, KK).
    /// Panics if the key has already been set.
    pub fn set_peer_static_public_key(mut self, public_key: &[u8]) -> Self {
        if self.config.handshake_handler_config.peer_static_public_key.is_none() {
            self.config.handshake_handler_config.peer_static_public_key = Some(public_key.to_vec());
        } else {
            panic!("peer public key has already been set");
        }
        self
    }

    /// Sets a custom [`EncryptorProvider`] for creating the session encryptor.
    ///
    /// This allows overriding the default [`OrderedChannelEncryptorProvider`].
    pub fn set_encryption_provider(
        mut self,
        encryptor_provider: Box<dyn EncryptorProvider>,
    ) -> Self {
        self.config.encryptor_config.encryptor_provider = encryptor_provider;
        self
    }

    /// Adds a [`SessionBinder`] used by this party to bind its attestation to
    /// the current session's handshake. The `attestation_id` associates this
    /// binder with a specific attestation flow/result, ensuring that the
    /// correct attestation context is bound.
    pub fn add_session_binder(
        mut self,
        attester_id: String,
        session_binder: Box<dyn SessionBinder>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::SelfUnidirectional
            ),
            "Session binding is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        self.config
            .handshake_handler_config
            .session_binders
            .insert(attester_id, session_binder.into());
        self
    }

    /// Adds a [`SessionBinder`] by reference, retaining ownership.
    /// See [`add_session_binder`] for details on `attestation_id`.
    pub fn add_session_binder_ref(
        mut self,
        attester_id: String,
        session_binder: &Arc<dyn SessionBinder>,
    ) -> Self {
        assert!(
            matches!(
                self.config.attestation_type,
                AttestationType::Bidirectional | AttestationType::SelfUnidirectional
            ),
            "Session binding is not supported for attestation type {:?}",
            self.config.attestation_type
        );
        self.config
            .handshake_handler_config
            .session_binders
            .insert(attester_id, session_binder.clone());
        self
    }

    /// Sets a custom [`LegacyVerifierResultsAggregator`] for combining legacy
    /// attestation verification results.
    ///
    /// This allows overriding the default
    /// [`DefaultLegacyVerifierResultsAggregator`].
    pub fn set_legacy_attestation_results_aggregator(
        mut self,
        aggregator: Box<dyn LegacyVerifierResultsAggregator>,
    ) -> Self {
        self.config.attestation_handler_config.legacy_attestation_results_aggregator = aggregator;
        self
    }

    /// Sets a custom [`AssertionResultsAggregator`] for combining assertion
    /// verification results.
    ///
    /// This allows overriding the default [`Empty`] aggregator.
    pub fn set_assertion_attestation_aggregator(
        mut self,
        aggregator: Box<dyn AssertionResultsAggregator>,
    ) -> Self {
        self.config.attestation_handler_config.assertion_attestation_aggregator = aggregator;
        self
    }

    /// Consumes the builder and returns the configured [`SessionConfig`].
    pub fn build(self) -> SessionConfig {
        assert!(
            self.config
                .attestation_handler_config
                .assertion_attestation_aggregator
                .is_compatible_with_configuration(
                    &self.config.attestation_handler_config.peer_assertion_verifiers
                ),
            "Assertion attestation aggregator is not compatible with the configured peer assertion verifiers",
        );
        self.config
    }
}

/// A container for a peer's attestation verifier and a provider for a verifier
/// for the session binding.
pub struct PeerAttestationVerifier {
    /// The [`AttestationVerifier`] used to verify the peer's
    /// [`EndorsedEvidence`].
    pub verifier: Arc<dyn AttestationVerifier>,
    /// A provider that creates a [`SessionBindingVerifier`] from the peer's
    /// successfully verified attestation results. This is used to verify that
    /// the peer has bound its attestation to the current session.
    pub binding_verifier_provider: Arc<dyn SessionBindingVerifierProvider>,
}

/// Configuration for the attestation phase of a session.
///
/// Instances are typically created and populated via the
/// [`SessionConfigBuilder`].
#[allow(dead_code)]
#[derive(Default)]
pub struct AttestationHandlerConfig {
    /// A map of attesters (keyed by `attestation_id`) used by this party to
    /// generate its own attestation [`Evidence`].
    pub self_attesters: BTreeMap<String, Arc<dyn Attester>>,
    /// A map of [`AssertionGenerator`]s (keyed by `assertion_id`) used by this
    /// party to generate its own [`Assertion`]. Not yet used.
    pub self_assertion_generators: BTreeMap<String, Arc<dyn AssertionGenerator>>,
    /// A map of endorsers (keyed by `attestation_id`) used by this party to
    /// generate [`Endorsements`] for its own [`Evidence`]. The key must match
    /// the `attestation_id` of the evidence being endorsed.
    pub self_endorsers: BTreeMap<String, Arc<dyn Endorser>>,
    /// A map of [`PeerAttestationVerifier`]s (keyed by `attestation_id`) used
    /// to verify [`EndorsedEvidence`] received from the peer. The key is
    /// used to select the correct verifier based on the `attestation_id`
    /// provided with the peer's evidence.
    pub peer_verifiers: BTreeMap<String, PeerAttestationVerifier>,
    /// A map of [`AssertionVerifier`]s (keyed by `assertion_id`) used to
    /// verify an [`Assertion`] received from the peer. Not yet used,
    pub peer_assertion_verifiers: BTreeMap<String, Arc<dyn AssertionVerifier>>,
    /// Logic to combine multiple attestation verification results in the legacy
    /// format (if the peer provides evidence from different attesters) into
    /// a single overall [`AttestationVerdict`]. Both
    /// `legacy_attestation_results_aggregator` and
    /// `assertion_attestation_aggregator` must succeed for the attestation to
    /// succeed.
    pub legacy_attestation_results_aggregator: Box<dyn LegacyVerifierResultsAggregator>,
    /// Logic to combine multiple assertion verification results (if the peer
    /// provides multiple assertions) into a single overall
    /// [`AttestationVerdict`]. Both `legacy_attestation_results_aggregator`
    /// and `assertion_attestation_aggregator` must succeed for the
    /// attestation to succeed.
    pub assertion_attestation_aggregator: Box<dyn AssertionResultsAggregator>,
}

impl Default for alloc::boxed::Box<dyn LegacyVerifierResultsAggregator> {
    fn default() -> Self {
        alloc::boxed::Box::new(DefaultLegacyVerifierResultsAggregator {})
    }
}

impl Default for alloc::boxed::Box<dyn AssertionResultsAggregator> {
    fn default() -> Self {
        alloc::boxed::Box::new(Empty {})
    }
}

/// Configuration for the cryptographic handshake phase of a session.
///
/// Instances are typically created and populated via the
/// [`SessionConfigBuilder`].
#[allow(dead_code)]
pub struct HandshakeHandlerConfig {
    /// Specifies the cryptographic handshake protocol to use (e.g., Noise KK,
    /// NK, NN).
    pub handshake_type: HandshakeType,
    /// This party's static private key. Required for certain handshake patterns
    /// (e.g., Noise IK where this party is the initiator, or Noise KK).
    pub self_static_private_key: Option<Box<dyn IdentityKeyHandle>>,
    /// The peer's static public key. Required for certain handshake patterns
    /// (e.g., Noise IK where this party is the responder, or Noise KK).
    pub peer_static_public_key: Option<Vec<u8>>,
    /// A map of [`SessionBinder`]s (keyed by `attestation_id`) used by this
    /// party to create cryptographic bindings. These bindings link this
    /// party's attestation (identified by `attestation_id`) to the current
    /// session's handshake hash.
    pub session_binders: BTreeMap<String, Arc<dyn SessionBinder>>,
}

/// Configuration for creating the session encryptor.
///
/// Instances are typically created and populated via the
/// [`SessionConfigBuilder`].
pub struct EncryptorConfig {
    /// A provider that creates an [`Encryptor`] instance once session keys are
    /// established from the handshake.
    pub encryptor_provider: Box<dyn EncryptorProvider>,
}
