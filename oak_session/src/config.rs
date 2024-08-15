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

use alloc::{boxed::Box, collections::BTreeMap, string::String, vec::Vec};

use anyhow::Error;
use oak_crypto::{encryptor::Encryptor, identity_key::IdentityKeyHandle};
use oak_proto_rust::oak::crypto::v1::SessionKeys;

use crate::{
    attestation::{AttestationType, AttestationVerifier, Attester},
    encryptors::OrderedChannelEncryptor,
    handshake::HandshakeType,
};

#[allow(dead_code)]
pub struct SessionConfig {
    pub attestation_provider_config: AttestationProviderConfig,
    pub handshaker_config: HandshakerConfig,
    pub encryptor_config: EncryptorConfig,
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

impl SessionConfigBuilder {
    fn new(attestation_type: AttestationType, handshake_type: HandshakeType) -> Self {
        let attestation_provider_config = AttestationProviderConfig {
            attestation_type,
            self_attesters: BTreeMap::new(),
            peer_verifiers: BTreeMap::new(),
        };

        let handshaker_config = HandshakerConfig {
            handshake_type,
            self_static_private_key: None,
            peer_static_public_key: None,
            peer_attestation_binding_public_key: None,
        };

        let encryptor_config = EncryptorConfig {
            encryptor_provider: Box::new(|sk| {
                <SessionKeys as TryInto<OrderedChannelEncryptor>>::try_into(sk)
                    .map(|v| Box::new(v) as Box<dyn Encryptor>)
            }),
        };

        let config =
            SessionConfig { attestation_provider_config, handshaker_config, encryptor_config };
        Self { config }
    }

    pub fn add_self_attester(mut self, attester_id: String, attester: Box<dyn Attester>) -> Self {
        self.config.attestation_provider_config.self_attesters.insert(attester_id, attester);
        self
    }

    pub fn add_peer_verifier(
        mut self,
        attester_id: String,
        verifier: Box<dyn AttestationVerifier>,
    ) -> Self {
        self.config.attestation_provider_config.peer_verifiers.insert(attester_id, verifier);
        self
    }

    pub fn set_self_private_key(mut self, private_key: Box<dyn IdentityKeyHandle>) -> Self {
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
        encryptor_provider: Box<dyn Fn(SessionKeys) -> Result<Box<dyn Encryptor>, Error>>,
    ) -> Self {
        self.config.encryptor_config.encryptor_provider = encryptor_provider;
        self
    }

    pub fn build(self) -> SessionConfig {
        self.config
    }
}

#[allow(dead_code)]
pub struct AttestationProviderConfig {
    pub attestation_type: AttestationType,
    pub self_attesters: BTreeMap<String, Box<dyn Attester>>,
    pub peer_verifiers: BTreeMap<String, Box<dyn AttestationVerifier>>,
}

#[allow(dead_code)]
pub struct HandshakerConfig {
    pub handshake_type: HandshakeType,
    // Used for authentication schemes where a static public key is pre-shared with the responder.
    pub self_static_private_key: Option<Box<dyn IdentityKeyHandle>>,
    // Used for authentication schemes where a responder's static public key is pre-shared with
    // the initiator.
    pub peer_static_public_key: Option<Vec<u8>>,
    // Public key that can be used to bind the attestation obtained from the peer to the handshake.
    pub peer_attestation_binding_public_key: Option<Vec<u8>>,
}

pub struct EncryptorConfig {
    pub encryptor_provider: Box<dyn Fn(SessionKeys) -> Result<Box<dyn Encryptor>, Error>>,
}
