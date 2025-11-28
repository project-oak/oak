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

use bytes::Buf;
use ciborium::Value;
use coset::cwt::ClaimName;
use oak_crypto::encryption_key::{EncryptionKey, generate_encryption_key_pair};
use oak_dice::cert::{SHA2_256_ID, generate_ecdsa_key_pair};
use oak_proto_rust::oak::attestation::v1::{Event, SystemLayerData};
use prost::Message;

/// Measures the system image and returns a corresponding event log entry.
pub fn create_system_layer_event<B: oak_attestation::MeasureDigest>(system_image: B) -> Event {
    let digest = system_image.measure_digest();
    Event {
        tag: "stage1".to_string(),
        event: Some(prost_types::Any {
            type_url: "type.googleapis.com/oak.attestation.v1.SystemLayerData".to_string(),
            value: SystemLayerData { system_image: Some(digest) }.encode_to_vec(),
        }),
    }
}

/// Creates a container event that includes image bytes and configuration
/// measurements and public keys used by the container.
pub fn create_container_event<A: Buf, B: Buf>(
    container_bytes: A,
    config_bytes: B,
    instance_public_keys: &InstancePublicKeys,
) -> Event {
    let container_digest = oak_attestation::MeasureDigest::measure_digest(container_bytes);
    let config_digest = oak_attestation::MeasureDigest::measure_digest(config_bytes);
    Event {
        tag: "ORCHESTRATOR".to_string(),
        event: Some(prost_types::Any {
            type_url: "type.googleapis.com/oak.attestation.v1.ContainerLayerData".to_string(),
            value: oak_proto_rust::oak::attestation::v1::ContainerLayerData {
                bundle: Some(container_digest),
                config: Some(config_digest),
                hybrid_encryption_public_key: instance_public_keys.encryption_public_key.to_vec(),
                signing_public_key: instance_public_keys
                    .signing_public_key
                    .to_sec1_bytes()
                    .to_vec(),
                session_binding_public_key: instance_public_keys
                    .session_binding_public_key
                    .to_sec1_bytes()
                    .to_vec(),
            }
            .encode_to_vec(),
        }),
    }
}

/// Measures the provided event and returns as an additional CWT claim.
pub fn create_container_dice_layer(event: &Event) -> oak_attestation::dice::LayerData {
    let encoded_event = event.encode_to_vec();
    let event_digest = oak_attestation::MeasureDigest::measure_digest(&encoded_event[..]);
    oak_attestation::LayerData {
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
    let (session_binding_key, session_binding_public_key) = generate_ecdsa_key_pair();
    (
        InstanceKeys { encryption_key, signing_key, session_binding_key },
        InstancePublicKeys {
            encryption_public_key,
            signing_public_key,
            session_binding_public_key,
        },
    )
}

pub struct InstanceKeys {
    pub encryption_key: EncryptionKey,
    pub signing_key: p256::ecdsa::SigningKey,
    pub session_binding_key: p256::ecdsa::SigningKey,
}

pub struct InstancePublicKeys {
    pub encryption_public_key: Vec<u8>,
    pub signing_public_key: p256::ecdsa::VerifyingKey,
    pub session_binding_public_key: p256::ecdsa::VerifyingKey,
}
