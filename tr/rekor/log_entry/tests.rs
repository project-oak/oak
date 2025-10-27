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

extern crate alloc;

use oak_proto_rust::oak::attestation::v1::{KeyType, VerifyingKey, VerifyingKeySet};
use serde_json::json;
use test_util::EndorsementData;

use super::*;
use crate::log_entry::{
    parse_rekor_log_entry, verify_rekor_log_entry_ecdsa, verify_rekor_signature, LogEntry,
};

/// Shorthand to create a reference value proto from ingredients.
fn create_verifying_key_set(public_key: &[u8]) -> VerifyingKeySet {
    let key = VerifyingKey {
        r#type: KeyType::EcdsaP256Sha256.into(),
        key_id: 1,
        raw: public_key.to_vec(),
    };
    VerifyingKeySet { keys: [key].to_vec(), ..Default::default() }
}

#[test]
fn test_verify_rekor_signature_success() {
    let d = EndorsementData::load();
    let log_entry = parse_rekor_log_entry(&d.log_entry).expect("could not parse log entry");

    let result = verify_rekor_signature(&log_entry, &d.rekor_public_key);

    assert!(result.is_ok());
}

#[test]
fn test_verify_rekor_log_entry_success() {
    let d = EndorsementData::load();
    let key_set = create_verifying_key_set(&d.rekor_public_key);

    let result = verify_rekor_log_entry(&d.log_entry, &key_set, &d.endorsement, 0);

    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_rekor_log_entry_failure() {
    // Deliberately invalidate the public key.
    let mut d = EndorsementData::load();
    d.rekor_public_key[0] += 1;
    let key_set = create_verifying_key_set(&d.rekor_public_key);

    let result = verify_rekor_log_entry(&d.log_entry, &key_set, &d.endorsement, 0);

    assert!(result.is_err());
}

#[test]
fn test_verify_rekor_log_entry_ecdsa_success() {
    let d = EndorsementData::load();

    let result = verify_rekor_log_entry_ecdsa(&d.log_entry, &d.rekor_public_key, &d.endorsement);

    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_from_cosign_bundle_missing_payload() {
    let bundle = json!({
        "SignedEntryTimestamp": "signature",
    });
    let bundle_str = serde_json::to_string(&bundle).unwrap();

    let result = LogEntry::from_cosign_bundle(&bundle_str);

    assert!(result.is_err());
}

#[test]
fn test_from_cosign_bundle_invalid_signature_base64() {
    let payload = json!({
        "body": "c29tZSBib2R5",
    });
    let bundle = json!({
        "Payload": payload,
        "SignedEntryTimestamp": "invalid-base64",
    });
    let bundle_str = serde_json::to_string(&bundle).unwrap();

    let result = LogEntry::from_cosign_bundle(&bundle_str);

    assert!(result.is_err());
}

// An actual bundle returned from pull_payload().
const REKOR_BUNDLE: &str = r###"{"SignedEntryTimestamp":"MEUCIFj09/fxhnbsGKn2y7wtnZFk3gOmcVVQeXcZWYxYnnvjAiEA6j+pNc1j5DdfKLFjb6u3yBU8IOzO3vD7DcobUiL1X/o=","Payload":{"body":"eyJhcGlWZXJzaW9uIjoiMC4wLjEiLCJraW5kIjoiaGFzaGVkcmVrb3JkIiwic3BlYyI6eyJkYXRhIjp7Imhhc2giOnsiYWxnb3JpdGhtIjoic2hhMjU2IiwidmFsdWUiOiI5NWM4YzE2MGM5ZDYxNzA4ZWRkYzkwNzg4MmQxYmE1OGNjNDg3YWZmNDViOWM1ODQ3OGQ5MmM0ZTA4MjAxOGNjIn19LCJzaWduYXR1cmUiOnsiY29udGVudCI6Ik1FVUNJUUM0NjVGQUJZNUwxUWREV3lJajJNTlJPRjMzN2E0YUhpUFFoRDdRS1NaMG1BSWdVcmJDYUh4NkMvUDE0bUsxYlkwMm9yL0tIYXdKdzRVSW00cUQwaU1UeC8wPSIsInB1YmxpY0tleSI6eyJjb250ZW50IjoiTFMwdExTMUNSVWRKVGlCUVZVSk1TVU1nUzBWWkxTMHRMUzBLVFVacmQwVjNXVWhMYjFwSmVtb3dRMEZSV1VsTGIxcEplbW93UkVGUlkwUlJaMEZGWjFaWE5FSnVkMDFZU0RGbFZDc3haMEpyUXl0RWNrZE9iMVZSWmdwWlpXTlBWeXRhS3pWUlZFSnFabGRqUVhCU01rNTVOVzlSVFZkVk5sWTJiRlJ6UmxKRFdXUlBNVlpJWkVGdmVHNWpVelZZVlROeWNucFJQVDBLTFMwdExTMUZUa1FnVUZWQ1RFbERJRXRGV1MwdExTMHRDZz09In19fX0=","integratedTime":1761334477,"logIndex":637763709,"logID":"c0d23d6ad406973f9559f3ba2d1ca01f84147d8ffc5b8445c224f98b9591801d"}}"###;

#[test]
fn test_from_cosign_bundle_parse_round_trip() {
    let expected = LogEntry::from_cosign_bundle(REKOR_BUNDLE).expect("failed to parse bundle");
    let serialized_expected = serialize_rekor_log_entry(&expected).expect("failed to serialize");
    let actual = parse_rekor_log_entry(&serialized_expected).expect("failed to reparse");
    let serialized_actual = serialize_rekor_log_entry(&actual).expect("failed to reserialize");
    assert_eq!(serialized_actual, serialized_expected);
}
