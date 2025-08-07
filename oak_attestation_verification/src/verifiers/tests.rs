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
//
// Tests attestation verification once with most endorsements populated
// and reference values verified via public keys, where the underlying
// endorsements are created and signed on the fly. For other tests (in
// particular negative ones) see verifier_tests.rs.

use std::collections::BTreeMap;

use oak_proto_rust::oak::attestation::v1::EventAttestationResults;

use crate::verifiers::verify_event_artifacts_uniqueness;

#[test]
fn test_verify_event_artifacts_uniqueness_succeeds() {
    let event_attestation_results = [
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
    ];

    assert!(verify_event_artifacts_uniqueness(&[]).is_ok());
    assert!(verify_event_artifacts_uniqueness(&event_attestation_results).is_ok());
}

#[test]
fn test_verify_event_artifacts_uniqueness_fails() {
    let event_attestation_results = [
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
                ("id_1".to_string(), b"artifact_1".to_vec()),
            ]
            .into_iter()
            .collect::<BTreeMap<String, Vec<u8>>>(),
        },
        EventAttestationResults {
            artifacts: [("id_5".to_string(), b"artifact_5".to_vec())]
                .into_iter()
                .collect::<BTreeMap<String, Vec<u8>>>(),
        },
    ];

    assert!(verify_event_artifacts_uniqueness(&event_attestation_results).is_err());
}
