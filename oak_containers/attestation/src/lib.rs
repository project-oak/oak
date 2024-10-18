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

extern crate alloc;

use alloc::{string::ToString, vec};

use anyhow::Context;
use ciborium::Value;
use coset::cwt::ClaimName;
use oak_crypto::{
    encryption_key::{generate_encryption_key_pair, EncryptionKey},
    encryptor::ServerEncryptor,
};
use oak_dice::cert::{generate_ecdsa_key_pair, SHA2_256_ID};
use oak_proto_rust::oak::{
    crypto::v1::EncryptedRequest, key_provisioning::v1::GroupKeys as GroupKeysProto,
};
use prost::Message;

/// Measures the downloaded container image bytes and configuration and returns
/// these as a vector of additional CWT claims.
pub fn measure_container_and_config(
    container_bytes: &[u8],
    config_bytes: &[u8],
) -> oak_attestation::dice::LayerData {
    let container_digest = oak_attestation::dice::MeasureDigest::measure_digest(&container_bytes);
    let config_digest = oak_attestation::dice::MeasureDigest::measure_digest(&config_bytes);
    let encoded_event = oak_proto_rust::oak::attestation::v1::Event {
        tag: "ORCHESTRATOR".to_string(),
        event: Some(prost_types::Any {
            type_url: "type.googleapis.com/oak.attestation.v1.ContainerLayerData".to_string(),
            value: oak_proto_rust::oak::attestation::v1::ContainerLayerData {
                bundle: Some(container_digest.clone()),
                config: Some(config_digest.clone()),
            }
            .encode_to_vec(),
        }),
    }
    .encode_to_vec();
    let event_digest =
        oak_attestation::dice::MeasureDigest::measure_digest(&encoded_event.as_slice());
    oak_attestation::dice::LayerData {
        additional_claims: vec![(
            ClaimName::PrivateUse(oak_dice::cert::EVENT_ID),
            Value::Map(vec![(
                Value::Integer(SHA2_256_ID.into()),
                Value::Bytes(event_digest.sha2_256),
            )]),
        )],
        encoded_event,
    }
}

pub fn generate_instance_keys() -> (InstanceKeys, InstancePublicKeys) {
    let (encryption_key, encryption_public_key) = generate_encryption_key_pair();
    let (signing_key, signing_public_key) = generate_ecdsa_key_pair();
    (
        InstanceKeys { encryption_key, signing_key },
        InstancePublicKeys { encryption_public_key, signing_public_key },
    )
}

pub struct InstanceKeys {
    pub encryption_key: EncryptionKey,
    pub signing_key: p256::ecdsa::SigningKey,
}

pub struct InstancePublicKeys {
    pub encryption_public_key: Vec<u8>,
    pub signing_public_key: p256::ecdsa::VerifyingKey,
}

impl InstanceKeys {
    pub fn generate_group_keys(&self) -> (GroupKeys, GroupPublicKeys) {
        let (group_encryption_key, group_encryption_public_key) = generate_encryption_key_pair();
        (
            GroupKeys { encryption_key: group_encryption_key },
            GroupPublicKeys { encryption_public_key: group_encryption_public_key },
        )
    }

    pub fn provide_group_keys(&self, group_keys: GroupKeysProto) -> anyhow::Result<GroupKeys> {
        // Create server encryptor for decrypting the group keys received from the
        // leader enclave.
        let encrypted_encryption_private_key = group_keys
            .encrypted_encryption_private_key
            .context("encrypted encryption key wasn't provided")?;

        // Decrypt group keys.
        let (_, mut decrypted_encryption_private_key, _) =
            ServerEncryptor::decrypt(&encrypted_encryption_private_key, &self.encryption_key)
                .context("couldn't decrypt the encryption private key")?;

        let group_encryption_key =
            EncryptionKey::deserialize(&mut decrypted_encryption_private_key)
                .context("couldn't deserialize private key")?;

        Ok(GroupKeys { encryption_key: group_encryption_key })
    }
}

pub struct GroupKeys {
    pub encryption_key: EncryptionKey,
}

pub struct GroupPublicKeys {
    pub encryption_public_key: Vec<u8>,
}

impl GroupKeys {
    /// Returns group encryption private key which was encrypted with the
    /// `peer_public_key`.
    pub fn encrypted_group_encryption_key(
        &self,
        peer_public_key: &[u8],
    ) -> anyhow::Result<EncryptedRequest> {
        self.encryption_key.encrypted_private_key(peer_public_key)
    }
}