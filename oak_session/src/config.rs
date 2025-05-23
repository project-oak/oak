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

use alloc::{boxed::Box, collections::BTreeMap, string::String, sync::Arc, vec::Vec};

use anyhow::Error;
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_crypto::{encryptor::Encryptor, identity_key::IdentityKeyHandle};
use oak_proto_rust::oak::crypto::v1::SessionKeys;

use crate::{
    attestation::{AttestationAggregator, AttestationType, DefaultAttestationAggregator},
    encryptors::OrderedChannelEncryptor,
    handshake::HandshakeType,
    key_extractor::{DefaultSigningKeyExtractor, KeyExtractor},
    session_binding::{
        SessionBinder, SessionBindingVerifierProvider, SignatureBindingVerifierProvider,
    },
};
#[allow(dead_code)]
pub struct SessionConfig {
    pub attestation_provider_config: AttestationProviderConfig,
    pub handshaker_config: HandshakerConfig,
    pub encryptor_config: EncryptorConfig,
    pub binding_verifier_providers: BTreeMap<String, Arc<dyn SessionBindingVerifierProvider>>,
}

impl SessionConfig {
    pub fn builder(
        attestation_type: AttestationType,
        handshake_type: HandshakeType,
    ) -> SessionConfigBuilder {
        SessionConfigBuilder::new(attestation_type, handshake_type)
    }
}

pub struct SessionConfigBuilder {
    config: SessionConfig,
}

pub trait EncryptorProvider: Send {
    fn provide_encryptor(&self, session_keys: SessionKeys) -> Result<Box<dyn Encryptor>, Error>;
}

pub struct OrderedChannelEncryptorProvider;

impl EncryptorProvider for OrderedChannelEncryptorProvider {
    fn provide_encryptor(&self, session_keys: SessionKeys) -> Result<Box<dyn Encryptor>, Error> {
        TryInto::<OrderedChannelEncryptor>::try_into(session_keys)
            .map(|v| Box::new(v) as Box<dyn Encryptor>)
    }
}

impl SessionConfigBuilder {
    fn new(attestation_type: AttestationType, handshake_type: HandshakeType) -> Self {
        let attestation_provider_config = AttestationProviderConfig {
            attestation_type,
            self_attesters: BTreeMap::new(),
            self_endorsers: BTreeMap::new(),
            peer_verifiers: BTreeMap::new(),
            attestation_aggregator: Box::new(DefaultAttestationAggregator {}),
        };

        let handshaker_config = HandshakerConfig {
            handshake_type,
            self_static_private_key: None,
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        };

        let encryptor_config =
            EncryptorConfig { encryptor_provider: Box::new(OrderedChannelEncryptorProvider) };

        let binding_verifier_providers = BTreeMap::new();

        let config = SessionConfig {
            attestation_provider_config,
            handshaker_config,
            encryptor_config,
            binding_verifier_providers,
        };
        Self { config }
    }

    /// Add an Attester that generates an Evidence for this TEE.
    /// `attester_id` is passed alongside the Evidence and will be used by the
    /// peer to pick the corresponding Verifier.
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc9334#name-attester>
    pub fn add_self_attester(mut self, attester_id: String, attester: Box<dyn Attester>) -> Self {
        self.config.attestation_provider_config.self_attesters.insert(attester_id, attester.into());
        self
    }

    /// Add an Attester but retain ownership of the object.
    pub fn add_self_attester_ref(
        mut self,
        attester_id: String,
        attester: &Arc<dyn Attester>,
    ) -> Self {
        self.config
            .attestation_provider_config
            .self_attesters
            .insert(attester_id, attester.clone());
        self
    }

    /// Add an Endorser that generates Endorsements for this TEE.
    /// Endorser will only endorse the Evidence generated by an Attester with
    /// the same ID as the `endorser_id`.
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc9334#name-endorser-reference-value-pr>
    pub fn add_self_endorser(mut self, endorser_id: String, endorser: Box<dyn Endorser>) -> Self {
        self.config.attestation_provider_config.self_endorsers.insert(endorser_id, endorser.into());
        self
    }

    /// Add an Endorser but retain ownership of the object
    pub fn add_self_endorser_ref(
        mut self,
        endorser_id: String,
        endorser: &Arc<dyn Endorser>,
    ) -> Self {
        self.config
            .attestation_provider_config
            .self_endorsers
            .insert(endorser_id, endorser.clone());
        self
    }

    /// Add an Attestation Verifier that will verify Evidence and Endorsements
    /// from the peer's TEE. Verifier only verifies Evidence and
    /// Endorsements with with the same ID as the `attester_id`. A default key
    /// extractor is used to bind the received evidence to the session.
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc9334#name-verifier>
    pub fn add_peer_verifier(
        mut self,
        attester_id: String,
        verifier: Box<dyn AttestationVerifier>,
    ) -> Self {
        self.config
            .attestation_provider_config
            .peer_verifiers
            .insert(attester_id.clone(), verifier.into());
        self.config.binding_verifier_providers.insert(
            attester_id,
            Arc::new(SignatureBindingVerifierProvider::new(Arc::new(
                DefaultSigningKeyExtractor {},
            ))),
        );
        self
    }

    /// Add an Attestation Verifier but retain ownership of the object.
    pub fn add_peer_verifier_ref(
        mut self,
        attester_id: String,
        verifier: &Arc<dyn AttestationVerifier>,
    ) -> Self {
        self.config
            .attestation_provider_config
            .peer_verifiers
            .insert(attester_id.clone(), verifier.clone());
        self.config.binding_verifier_providers.insert(
            attester_id,
            Arc::new(SignatureBindingVerifierProvider::new(Arc::new(
                DefaultSigningKeyExtractor {},
            ))),
        );
        self
    }

    /// Add an Attestation Verifier with the custom key extractor to extract the
    /// key to bind the attestation to the session. The verifier will verify
    /// Evidence and Endorsements from the peer's TEE, and the key extractor
    /// will be used to extract the binding key from the evidence. Verifier only
    /// verifies Evidence and Endorsements with with the same ID as the
    /// `attester_id`.
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc9334#name-verifier>
    pub fn add_peer_verifier_with_key_extractor(
        mut self,
        attester_id: String,
        verifier: Box<dyn AttestationVerifier>,
        key_extractor: Box<dyn KeyExtractor>,
    ) -> Self {
        self.config
            .attestation_provider_config
            .peer_verifiers
            .insert(attester_id.clone(), verifier.into());
        self.config.binding_verifier_providers.insert(
            attester_id,
            Arc::new(SignatureBindingVerifierProvider::new(key_extractor.into())),
        );
        self
    }

    /// Add an Attestation Verifier with the custom key extractor but retain
    /// ownership of the objects.
    pub fn add_peer_verifier_with_key_extractor_ref(
        mut self,
        attester_id: String,
        verifier: &Arc<dyn AttestationVerifier>,
        key_extractor: &Arc<dyn KeyExtractor>,
    ) -> Self {
        self.config
            .attestation_provider_config
            .peer_verifiers
            .insert(attester_id.clone(), verifier.clone());
        self.config.binding_verifier_providers.insert(
            attester_id,
            Arc::new(SignatureBindingVerifierProvider::new(key_extractor.clone())),
        );
        self
    }

    /// Add an Attestation Verifier with the custom binding verifier provider to
    /// extract the key to bind the attestation to the session. The verifier
    /// will verify Evidence and Endorsements from the peer's TEE, and the
    /// binding verifier provider will create an object that can ensure binding
    /// between the evidence and the session. Verifier only verifies Evidence
    /// and Endorsements with with the same ID as the `attester_id`.
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc9334#name-verifier>
    pub fn add_peer_verifier_with_binding_verifier_provider(
        mut self,
        attester_id: String,
        verifier: Box<dyn AttestationVerifier>,
        binding_verifier_provider: Box<dyn SessionBindingVerifierProvider>,
    ) -> Self {
        self.config
            .attestation_provider_config
            .peer_verifiers
            .insert(attester_id.clone(), verifier.into());
        self.config
            .binding_verifier_providers
            .insert(attester_id, binding_verifier_provider.into());
        self
    }

    /// Add an Attestation Verifier with the custom binding verifier provider
    /// but retain ownership of the objects.
    pub fn add_peer_verifier_with_binding_verifier_provider_ref(
        mut self,
        attester_id: String,
        verifier: &Arc<dyn AttestationVerifier>,
        binding_verifier_provider: &Arc<dyn SessionBindingVerifierProvider>,
    ) -> Self {
        self.config
            .attestation_provider_config
            .peer_verifiers
            .insert(attester_id.clone(), verifier.clone());
        self.config
            .binding_verifier_providers
            .insert(attester_id, binding_verifier_provider.clone());
        self
    }

    pub fn set_self_static_private_key(mut self, private_key: Box<dyn IdentityKeyHandle>) -> Self {
        if self.config.handshaker_config.self_static_private_key.is_none() {
            self.config.handshaker_config.self_static_private_key = Some(private_key);
        } else {
            panic!("self private key has already been set");
        }
        self
    }

    pub fn set_peer_static_public_key(mut self, public_key: &[u8]) -> Self {
        if self.config.handshaker_config.peer_static_public_key.is_none() {
            self.config.handshaker_config.peer_static_public_key = Some(public_key.to_vec());
        } else {
            panic!("peer public key has already been set");
        }
        self
    }

    pub fn set_encryption_provider(
        mut self,
        encryptor_provider: Box<dyn EncryptorProvider>,
    ) -> Self {
        self.config.encryptor_config.encryptor_provider = encryptor_provider;
        self
    }

    pub fn add_session_binder(
        mut self,
        attester_id: String,
        session_binder: Box<dyn SessionBinder>,
    ) -> Self {
        self.config.handshaker_config.session_binders.insert(attester_id, session_binder.into());
        self
    }

    pub fn add_session_binder_ref(
        mut self,
        attester_id: String,
        session_binder: &Arc<dyn SessionBinder>,
    ) -> Self {
        self.config.handshaker_config.session_binders.insert(attester_id, session_binder.clone());
        self
    }

    pub fn build(self) -> SessionConfig {
        self.config
    }
}

#[allow(dead_code)]
pub struct AttestationProviderConfig {
    pub attestation_type: AttestationType,
    pub self_attesters: BTreeMap<String, Arc<dyn Attester>>,
    pub self_endorsers: BTreeMap<String, Arc<dyn Endorser>>,
    pub peer_verifiers: BTreeMap<String, Arc<dyn AttestationVerifier>>,
    pub attestation_aggregator: Box<dyn AttestationAggregator>,
}

#[allow(dead_code)]
pub struct HandshakerConfig {
    pub handshake_type: HandshakeType,
    // Used for authentication schemes where a static public key is pre-shared with the responder.
    pub self_static_private_key: Option<Box<dyn IdentityKeyHandle>>,
    // Used for authentication schemes where a responder's static public key is pre-shared with
    // the initiator.
    pub peer_static_public_key: Option<Vec<u8>>,
    // Session binders to bind the handshake hash to the previously received attestation data,
    // keyed by the attestation type.
    pub session_binders: BTreeMap<String, Arc<dyn SessionBinder>>,
}

pub struct EncryptorConfig {
    pub encryptor_provider: Box<dyn EncryptorProvider>,
}
