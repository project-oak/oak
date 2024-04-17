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

use std::fs;

use oak_attestation_verification::{
    claims::parse_endorsement_statement,
    endorsement::{
        verify_binary_endorsement, verify_endorsement_statement, verify_endorser_public_key,
    },
    rekor::{verify_rekor_log_entry, verify_rekor_signature},
    util::convert_pem_to_raw,
};

// The digest of the endorsement under ENDORSEMENT_PATH.
const ENDORSEMENT_PATH: &str = "testdata/endorsement.json";
const SIGNATURE_PATH: &str = "testdata/endorsement.json.sig";

const ENDORSER_PUBLIC_KEY_PATH: &str = "testdata/oak_containers_stage1.pem";
const LOG_ENTRY_PATH: &str = "testdata/logentry.json";

// Public key of the Rekor instance hosted by sigstore.dev. It is downloaded
// from https://rekor.sigstore.dev/api/v1/log/publicKey.
const REKOR_PUBLIC_KEY_PATH: &str = "testdata/rekor_public_key.pem";

// Pretend the tests run at this time: 1 March 2024, 12:00 UTC
const NOW_UTC_MILLIS: i64 = 1709294400000;

struct TestData {
    endorsement: Vec<u8>,
    signature: Vec<u8>,
    log_entry: Vec<u8>,
    endorser_public_key: Vec<u8>,
    rekor_public_key: Vec<u8>,
}

fn load_testdata() -> TestData {
    let endorsement = fs::read(ENDORSEMENT_PATH).expect("couldn't read endorsement");
    let signature = fs::read(SIGNATURE_PATH).expect("couldn't read signature");
    let log_entry = fs::read(LOG_ENTRY_PATH).expect("couldn't read log entry");
    let endorser_public_key_pem =
        fs::read_to_string(ENDORSER_PUBLIC_KEY_PATH).expect("couldn't read endorser public key");
    let rekor_public_key_pem =
        fs::read_to_string(REKOR_PUBLIC_KEY_PATH).expect("couldn't read rekor public key");

    let endorser_public_key = convert_pem_to_raw(endorser_public_key_pem.as_str())
        .expect("failed to convert endorser key");
    let rekor_public_key =
        convert_pem_to_raw(&rekor_public_key_pem).expect("failed to convert Rekor key");

    TestData { endorsement, signature, log_entry, endorser_public_key, rekor_public_key }
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
        &testdata.signature,
        &testdata.log_entry,
        &testdata.endorser_public_key,
        &testdata.rekor_public_key,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_with_invalid_endorser_public_key() {
    let testdata = load_testdata();

    let result = verify_binary_endorsement(
        NOW_UTC_MILLIS,
        &testdata.endorsement,
        &testdata.signature,
        &testdata.log_entry,
        // NB: We use the wrong key deliberately.
        &testdata.rekor_public_key,
        &testdata.rekor_public_key,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_with_invalid_rekor_public_key() {
    let testdata = load_testdata();

    let result = verify_binary_endorsement(
        NOW_UTC_MILLIS,
        &testdata.endorsement,
        &testdata.signature,
        &testdata.log_entry,
        &testdata.endorser_public_key,
        // NB: We use the wrong key deliberately.
        &testdata.endorser_public_key,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_with_rekor_key_but_no_log_entry() {
    let testdata = load_testdata();

    let result = verify_binary_endorsement(
        NOW_UTC_MILLIS,
        &testdata.endorsement,
        &testdata.signature,
        &Vec::new(),
        &testdata.endorser_public_key,
        &testdata.rekor_public_key,
    );
    assert!(result.is_err(), "{:?}", result);
}
