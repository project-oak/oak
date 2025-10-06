//
// Copyright 2025 The Project Oak Authors
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

//! Provides utilities to process the attestation results.

#![no_std]

extern crate alloc;

use alloc::{string::ToString, vec::Vec};

use oak_proto_rust::oak::attestation::v1::{AttestationResults, EventAttestationResults};

/// Key for the initial measurement of stage0.
const INITIAL_MEASUREMENT_ID: &str = "initial-measurement";

/// Denotes an artifact ID of a public key used to verify the Noise handshake
/// transcript signature.
const SESSION_BINDING_PUBLIC_KEY_ID: &str = "oak-session-binding-public-key:ecdsa-p256";

/// Denotes an artifact ID of a key to encrypt a single message with hybrid
/// encryption before sending it to the enclave.
const HYBRID_ENCRYPTION_PUBLIC_KEY_ID: &str = "oak-hybrid-encryption-public-key:X25519";

/// Denotes an artifact ID of a key used to verify artifacts generated and
/// signed by the enclave.
const SIGNING_PUBLIC_KEY_ID: &str = "oak-signing-public-key:ecdsa-p256";

pub fn get_initial_measurement(results: &EventAttestationResults) -> Option<&Vec<u8>> {
    results.artifacts.get(INITIAL_MEASUREMENT_ID)
}

pub fn set_initial_measurement(results: &mut EventAttestationResults, key: &[u8]) {
    results.artifacts.insert(INITIAL_MEASUREMENT_ID.to_string(), key.to_vec());
}

pub fn get_session_binding_public_key(results: &AttestationResults) -> Option<&Vec<u8>> {
    get_event_artifact(results, SESSION_BINDING_PUBLIC_KEY_ID)
}

pub fn set_session_binding_public_key(results: &mut EventAttestationResults, key: &[u8]) {
    results.artifacts.insert(SESSION_BINDING_PUBLIC_KEY_ID.to_string(), key.to_vec());
}

pub fn get_hybrid_encryption_public_key(results: &AttestationResults) -> Option<&Vec<u8>> {
    get_event_artifact(results, HYBRID_ENCRYPTION_PUBLIC_KEY_ID)
}

pub fn set_hybrid_encryption_public_key(results: &mut EventAttestationResults, key: &[u8]) {
    results.artifacts.insert(HYBRID_ENCRYPTION_PUBLIC_KEY_ID.to_string(), key.to_vec());
}

pub fn get_signing_public_key(results: &AttestationResults) -> Option<&Vec<u8>> {
    get_event_artifact(results, SIGNING_PUBLIC_KEY_ID)
}

pub fn set_signing_public_key(results: &mut EventAttestationResults, key: &[u8]) {
    results.artifacts.insert(SIGNING_PUBLIC_KEY_ID.to_string(), key.to_vec());
}

/// Returns a reference to the event artifact from `attestation_results` with a
/// given `artifact_id`.
pub fn get_event_artifact<'a>(
    attestation_results: &'a AttestationResults,
    artifact_id: &str,
) -> Option<&'a Vec<u8>> {
    attestation_results
        .event_attestation_results
        .iter()
        .find_map(|event| event.artifacts.get(artifact_id))
}

#[cfg(test)]
mod tests {
    use alloc::collections::BTreeMap;

    use oak_proto_rust::oak::attestation::v1::EventAttestationResults;

    use super::*;

    #[test]
    fn test_get_event_artifact() {
        let empty_results = AttestationResults { ..Default::default() };
        let results = AttestationResults {
            event_attestation_results: vec![
                EventAttestationResults {
                    artifacts: [
                        ("id_1".to_string(), b"artifact_1".to_vec()),
                        ("id_2".to_string(), b"artifact_2".to_vec()),
                    ]
                    .into_iter()
                    .collect::<BTreeMap<String, Vec<u8>>>(),
                },
                EventAttestationResults {
                    artifacts: [
                        ("id_3".to_string(), b"artifact_3".to_vec()),
                        ("id_4".to_string(), b"artifact_4".to_vec()),
                    ]
                    .into_iter()
                    .collect::<BTreeMap<String, Vec<u8>>>(),
                },
                EventAttestationResults {
                    artifacts: [("id_5".to_string(), b"artifact_5".to_vec())]
                        .into_iter()
                        .collect::<BTreeMap<String, Vec<u8>>>(),
                },
            ],
            ..Default::default()
        };

        assert!(get_event_artifact(&empty_results, "id_1").is_none());

        let artifact_1 = get_event_artifact(&results, "id_1");
        assert!(artifact_1.is_some());
        assert_eq!(*artifact_1.unwrap(), b"artifact_1".to_vec());

        let artifact_5 = get_event_artifact(&results, "id_5");
        assert!(artifact_5.is_some());
        assert_eq!(*artifact_5.unwrap(), b"artifact_5".to_vec());

        assert!(get_event_artifact(&results, "id_999").is_none());
    }
}
