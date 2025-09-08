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

//! Provides accessors to attestation results.

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

/// Returns the session binding key artifact contained in the event results,
/// or an error whenever it is missing or not unique.
pub fn unique_session_binding_public_key(
    results: &AttestationResults,
) -> Result<&Vec<u8>, &'static str> {
    unique_event_artifact(results, SESSION_BINDING_PUBLIC_KEY_ID)
}

pub fn set_session_binding_public_key(results: &mut EventAttestationResults, key: &[u8]) {
    results.artifacts.insert(SESSION_BINDING_PUBLIC_KEY_ID.to_string(), key.to_vec());
}

/// Returns the hybrid encryption key artifact contained in the event results,
/// or an error whenever it is missing or not unique.
pub fn unique_hybrid_encryption_public_key(
    results: &AttestationResults,
) -> Result<&Vec<u8>, &'static str> {
    unique_event_artifact(results, HYBRID_ENCRYPTION_PUBLIC_KEY_ID)
}

pub fn get_hybrid_encryption_public_key(results: &EventAttestationResults) -> Option<&Vec<u8>> {
    results.artifacts.get(HYBRID_ENCRYPTION_PUBLIC_KEY_ID)
}

pub fn set_hybrid_encryption_public_key(results: &mut EventAttestationResults, key: &[u8]) {
    results.artifacts.insert(HYBRID_ENCRYPTION_PUBLIC_KEY_ID.to_string(), key.to_vec());
}

/// Returns the signing key artifact contained in the attestation results,
/// or an error whenever it is missing or not unique.
pub fn unique_signing_public_key(results: &AttestationResults) -> Result<&Vec<u8>, &'static str> {
    unique_event_artifact(results, SIGNING_PUBLIC_KEY_ID)
}

pub fn set_signing_public_key(results: &mut EventAttestationResults, key: &[u8]) {
    results.artifacts.insert(SIGNING_PUBLIC_KEY_ID.to_string(), key.to_vec());
}

/// Returns a reference to the event artifact in the attestation results
/// specified by the given ID, or an error if that reference does not exist,
/// or if there is more than a single reference (`artifact_id` key exists
/// in results from multiple events).
fn unique_event_artifact<'a>(
    results: &'a AttestationResults,
    artifact_id: &str,
) -> Result<&'a Vec<u8>, &'static str> {
    let mut iter =
        results.event_attestation_results.iter().filter_map(|e| e.artifacts.get(artifact_id));
    let first = iter.next();
    if first.is_none() {
        return Err("missing artifact");
    }
    if iter.next().is_some() {
        return Err("duplicate artifact");
    }
    Ok(first.unwrap())
}

#[cfg(test)]
mod tests {
    use alloc::{collections::BTreeMap, string::String, vec};

    use oak_proto_rust::oak::attestation::v1::EventAttestationResults;

    use super::*;

    #[test]
    fn test_unique_event_artifact() {
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

        assert!(unique_event_artifact(&empty_results, "id_1").is_err());

        let artifact_1 = unique_event_artifact(&results, "id_1");
        assert!(artifact_1.is_ok());
        assert_eq!(*artifact_1.unwrap(), b"artifact_1".to_vec());

        let artifact_5 = unique_event_artifact(&results, "id_5");
        assert!(artifact_5.is_ok());
        assert_eq!(*artifact_5.unwrap(), b"artifact_5".to_vec());

        assert!(unique_event_artifact(&results, "id_999").is_err());
    }
}
