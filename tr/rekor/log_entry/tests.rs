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

use oak_proto_rust::oak::attestation::v1::{KeyType, VerifyingKey, VerifyingKeySet};
use test_util::EndorsementData;

use crate::log_entry::{
    parse_rekor_log_entry, verify_rekor_log_entry, verify_rekor_log_entry_ecdsa,
    verify_rekor_signature,
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
