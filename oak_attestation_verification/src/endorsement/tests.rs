//
// Copyright 2022 The Project Oak Authors
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
#[cfg(test)]
extern crate std;

use alloc::vec::Vec;

use test_util::endorsement_data::EndorsementData;

use crate::endorsement::verify_binary_endorsement;

#[test]
fn test_verify_binary_endorsement_success() {
    let d = EndorsementData::load();

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &d.signature,
        &d.log_entry,
        &d.endorser_public_key,
        &d.rekor_public_key,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_with_empty_signature() {
    let d = EndorsementData::load();

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &Vec::new(),
        &d.log_entry,
        &d.endorser_public_key,
        &d.rekor_public_key,
    );
    assert!(result.is_err(), "{:?}", result);

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &Vec::new(),
        &Vec::new(),
        &d.endorser_public_key,
        &Vec::new(),
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_with_invalid_signature() {
    let mut d = EndorsementData::load();

    d.signature[0] ^= 1;

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &d.signature,
        &d.log_entry,
        &d.endorser_public_key,
        &d.rekor_public_key,
    );
    assert!(result.is_err(), "{:?}", result);

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &d.signature,
        &Vec::new(),
        &d.endorser_public_key,
        &Vec::new(),
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_with_empty_endorser_public_key() {
    let d = EndorsementData::load();

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &d.signature,
        &d.log_entry,
        &Vec::new(),
        &d.rekor_public_key,
    );
    assert!(result.is_err(), "{:?}", result);

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &d.signature,
        &Vec::new(),
        &Vec::new(),
        &Vec::new(),
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_with_invalid_endorser_public_key() {
    let d = EndorsementData::load();

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &d.signature,
        &d.log_entry,
        // NB: We use the wrong key deliberately.
        &d.rekor_public_key,
        &d.rekor_public_key,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_with_invalid_rekor_public_key() {
    let d = EndorsementData::load();

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &d.signature,
        &d.log_entry,
        &d.endorser_public_key,
        // NB: We use the wrong key deliberately.
        &d.endorser_public_key,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_with_rekor_key_but_no_log_entry() {
    let d = EndorsementData::load();

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &d.signature,
        &Vec::new(),
        &d.endorser_public_key,
        &d.rekor_public_key,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_succeeds_with_no_rekor_key() {
    let d = EndorsementData::load();

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &d.signature,
        &d.log_entry,
        &d.endorser_public_key,
        &Vec::new(),
    );
    assert!(result.is_ok(), "{:?}", result);

    let result = verify_binary_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.endorsement,
        &d.signature,
        &Vec::new(),
        &d.endorser_public_key,
        &Vec::new(),
    );
    assert!(result.is_ok(), "{:?}", result);
}
