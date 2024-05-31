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

use alloc::{vec, vec::Vec};

use crate::{
    attestation::{AttestationType, AttestationVerifier, Attester},
    handshake::{EncryptionKeyHandle, HandshakeType},
};

#[allow(dead_code)]
pub struct SessionConfig<'a> {
    attestation_provider_config: AttestationProviderConfig<'a>,
    handshaker_config: HandshakerConfig<'a>,
}

impl<'a> SessionConfig<'a> {
    pub fn builder(attestation_type: AttestationType) -> SessionConfigBuilder<'a> {
        SessionConfigBuilder::new(attestation_type)
    }
}

pub struct SessionConfigBuilder<'a> {
    config: SessionConfig<'a>,
}

impl<'a> SessionConfigBuilder<'a> {
    fn new(attestation_type: AttestationType) -> Self {
        let handshake_type = match attestation_type {
            AttestationType::Bidirectional => HandshakeType::NoiseKK,
            AttestationType::SelfUnidirectional => HandshakeType::NoiseKN,
            AttestationType::PeerUnidirectional => HandshakeType::NoiseNK,
        };

        let attestation_provider_config = AttestationProviderConfig {
            attestation_type,
            self_attesters: vec![],
            peer_verifiers: vec![],
        };

        let handshaker_config = HandshakerConfig {
            handshake_type,
            self_static_private_key: None,
            peer_static_public_key: None,
        };

        let config = SessionConfig { attestation_provider_config, handshaker_config };
        Self { config }
    }

    pub fn add_self_attester(mut self, attester: &'a dyn Attester) -> Self {
        self.config.attestation_provider_config.self_attesters.push(attester);
        self
    }

    pub fn add_peer_verifier(mut self, verifier: &'a dyn AttestationVerifier) -> Self {
        self.config.attestation_provider_config.peer_verifiers.push(verifier);
        self
    }

    pub fn set_self_private_key(mut self, private_key: &'a dyn EncryptionKeyHandle) -> Self {
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

    pub fn build(self) -> SessionConfig<'a> {
        self.config
    }
}

#[allow(dead_code)]
pub struct AttestationProviderConfig<'a> {
    pub attestation_type: AttestationType,
    pub self_attesters: Vec<&'a dyn Attester>,
    pub peer_verifiers: Vec<&'a dyn AttestationVerifier>,
}

#[allow(dead_code)]
pub struct HandshakerConfig<'a> {
    pub handshake_type: HandshakeType,
    pub self_static_private_key: Option<&'a dyn EncryptionKeyHandle>,
    pub peer_static_public_key: Option<Vec<u8>>,
}
