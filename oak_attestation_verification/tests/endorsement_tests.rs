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

extern crate alloc;

use alloc::vec::Vec;
use std::fs;

use oak_attestation_verification::{
    claims::parse_endorsement_statement,
    endorsement::{
        verify_binary_digest, verify_binary_endorsement, verify_endorsement_statement,
        verify_endorser_public_key,
    },
    rekor::{verify_rekor_log_entry, verify_rekor_signature},
    util::{convert_pem_to_raw, MatchResult},
};

use oak_attestation_proto::oak::HexDigest;

const BINARY_DIGEST: &str = "39051983bbb600bbfb91bd22ee4c976420f8f0c6a895fd083dcb0d153ddd5fd6";
const ENDORSEMENT_PATH: &str = "testdata/endorsement.json";

// Public key fetched from Google Cloud KMS, associated with the signing key that was used for
// signing the endorsement statement.
const ENDORSER_PUBLIC_KEY_PATH: &str = "testdata/oak-development.pem";

// LogEntry downloaded from
// https://rekor.sigstore.dev/api/v1/log/entries/24296fb24b8ad77a51d549703a3a1c2dd2639ba49617fc563854031cb93e6d354e7b005065c334a8.
// This LogEntry was created by signing the example endorsement file above, using google-cloud
// KMS, and uploading it to Rekor (https://rekor.sigstore.dev) using `rekor-cli`, as described
// in https://github.com/sigstore/rekor/blob/main/types.md#pkixx509.
// The resulting entry in Rekor has UUID
// `24296fb24b8ad77a51d549703a3a1c2dd2639ba49617fc563854031cb93e6d354e7b005065c334a8` and
// logIndex 30891523. The body of LogEntry can be fetched using `rekor-cli get --log-index
// 30891523`.
const LOG_ENTRY_PATH: &str = "testdata/logentry.json";

// Public key of the Rekor instance hosted by sigstore.dev. It is downloaded from
// https://rekor.sigstore.dev/api/v1/log/publicKey.
const REKOR_PUBLIC_KEY_PATH: &str = "testdata/rekor_public_key.pem";

// Pretend the tests run at this time: 1 Nov 2023, 9:00 UTC
const NOW_UTC_MILLIS: i64 = 1698829200000;

struct TestData {
    endorsement: Vec<u8>,
    log_entry: Vec<u8>,
    endorser_public_key: Vec<u8>,
    rekor_public_key: Vec<u8>,
}

fn create_hex_digest() -> HexDigest {
    HexDigest {
        sha2_256: BINARY_DIGEST.to_owned(),
        ..Default::default()
    }
}

fn load_testdata() -> TestData {
    let endorsement = fs::read(ENDORSEMENT_PATH).expect("couldn't read endorsement");
    let log_entry = fs::read(LOG_ENTRY_PATH).expect("couldn't read log entry");
    let endorser_public_key_pem =
        fs::read_to_string(ENDORSER_PUBLIC_KEY_PATH).expect("couldn't read endorser public key");
    let rekor_public_key_pem =
        fs::read_to_string(REKOR_PUBLIC_KEY_PATH).expect("couldn't read rekor public key");

    let endorser_public_key = convert_pem_to_raw(endorser_public_key_pem.as_str())
        .expect("failed to convert endorser key");
    let rekor_public_key =
        convert_pem_to_raw(&rekor_public_key_pem).expect("failed to convert Rekor key");

    TestData {
        endorsement,
        log_entry,
        endorser_public_key,
        rekor_public_key,
    }
}

#[test]
fn test_verify_binary_digest_same() {
    let testdata = load_testdata();
    let expected = create_hex_digest();
    let result = verify_binary_digest(&testdata.endorsement, &expected);
    assert!(result.is_ok_and(|m| m == MatchResult::SAME));
}

#[test]
fn test_verify_binary_digest_different() {
    let testdata = load_testdata();
    let expected = HexDigest {
        psha2: BINARY_DIGEST.to_owned(),
        sha1: BINARY_DIGEST.to_owned(),
        sha2_256: "00000bad000digestb91bd22ee4c976420f8f0c6a895fd083dcb0d0000000000".to_owned(),
        sha2_512: BINARY_DIGEST.to_owned(),
        sha3_512: BINARY_DIGEST.to_owned(),
        sha3_384: BINARY_DIGEST.to_owned(),
        sha3_256: BINARY_DIGEST.to_owned(),
        sha3_224: BINARY_DIGEST.to_owned(),
        sha2_384: BINARY_DIGEST.to_owned(),
    };
    let result = verify_binary_digest(&testdata.endorsement, &expected);
    assert!(result.is_ok_and(|m| m == MatchResult::DIFFERENT));
}

#[test]
fn test_verify_binary_digest_undecidable() {
    let testdata = load_testdata();
    // Fill all hashes with something (whatever) but leave sha2_256 empty.
    let expected = HexDigest {
        psha2: BINARY_DIGEST.to_owned(),
        sha1: BINARY_DIGEST.to_owned(),
        sha2_256: "".to_owned(),
        sha2_512: BINARY_DIGEST.to_owned(),
        sha3_512: BINARY_DIGEST.to_owned(),
        sha3_384: BINARY_DIGEST.to_owned(),
        sha3_256: BINARY_DIGEST.to_owned(),
        sha3_224: BINARY_DIGEST.to_owned(),
        sha2_384: BINARY_DIGEST.to_owned(),
    };
    let result = verify_binary_digest(&testdata.endorsement, &expected);
    assert!(result.is_ok_and(|m| m == MatchResult::UNDECIDABLE));
}

#[test]
fn test_verify_rekor_signature() {
    let testdata = load_testdata();
    let result = verify_rekor_signature(&testdata.log_entry, &testdata.rekor_public_key);
    assert!(result.is_ok());
}

#[test]
fn test_verify_rekor_log_entry() {
    let testdata = load_testdata();

    let result = verify_rekor_log_entry(
        &testdata.log_entry,
        &testdata.rekor_public_key,
        &testdata.endorsement,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_statement() {
    let testdata = load_testdata();
    let statement = parse_endorsement_statement(&testdata.endorsement)
        .expect("could not parse endorsement statement");
    let result = verify_endorsement_statement(NOW_UTC_MILLIS, &statement);
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_endorser_public_key() {
    let testdata = load_testdata();

    let result = verify_endorser_public_key(&testdata.log_entry, &testdata.endorser_public_key);
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement() {
    let testdata = load_testdata();

    let result = verify_binary_endorsement(
        NOW_UTC_MILLIS,
        &testdata.endorsement,
        &testdata.log_entry,
        &testdata.endorser_public_key,
        &testdata.rekor_public_key,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_with_invalid_rekor_public_key() {
    let testdata = load_testdata();

    let result = verify_binary_endorsement(
        NOW_UTC_MILLIS,
        &testdata.endorsement,
        &testdata.log_entry,
        &testdata.endorser_public_key,
        // NB: We use the wrong key deliberately.
        &testdata.endorser_public_key,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_when_missing_rekor_entry() {
    let testdata = load_testdata();

    let result = verify_binary_endorsement(
        NOW_UTC_MILLIS,
        &testdata.endorsement,
        &Vec::new(),
        &testdata.endorser_public_key,
        &Vec::new(),
    );
    assert!(result.is_err(), "{:?}", result);
}
