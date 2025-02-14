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
#[cfg(test)]
extern crate std;

use alloc::vec::Vec;
use std::fs;

use oak_file_utils::data_path;

use crate::{
    rekor::{parse_rekor_log_entry, verify_rekor_log_entry_ecdsa, verify_rekor_signature},
    util::convert_pem_to_raw,
};

const ENDORSEMENT_PATH: &str = "oak_attestation_verification/testdata/endorsement.json";
const LOG_ENTRY_PATH: &str = "oak_attestation_verification/testdata/logentry.json";

// Public key of the Rekor instance hosted by sigstore.dev. It is downloaded
// from https://rekor.sigstore.dev/api/v1/log/publicKey.
const REKOR_PUBLIC_KEY_PATH: &str = "oak_attestation_verification/testdata/rekor_public_key.pem";

struct TestData {
    endorsement: Vec<u8>,
    log_entry: Vec<u8>,
    rekor_public_key: Vec<u8>,
}

fn load_testdata() -> TestData {
    let endorsement = fs::read(data_path(ENDORSEMENT_PATH)).expect("couldn't read endorsement");
    let log_entry = fs::read(data_path(LOG_ENTRY_PATH)).expect("couldn't read log entry");
    let rekor_public_key_pem = fs::read_to_string(data_path(REKOR_PUBLIC_KEY_PATH))
        .expect("couldn't read rekor public key");

    let rekor_public_key =
        convert_pem_to_raw(&rekor_public_key_pem).expect("failed to convert Rekor key");

    TestData { endorsement, log_entry, rekor_public_key }
}

#[test]
fn test_verify_rekor_signature_success() {
    let testdata = load_testdata();
    let log_entry = parse_rekor_log_entry(&testdata.log_entry).expect("could not parse log entry");

    let result = verify_rekor_signature(&log_entry, &testdata.rekor_public_key);

    assert!(result.is_ok());
}

#[test]
fn test_verify_rekor_log_entry_success() {
    let testdata = load_testdata();

    let result = verify_rekor_log_entry_ecdsa(
        &testdata.log_entry,
        &testdata.rekor_public_key,
        &testdata.endorsement,
    );

    assert!(result.is_ok(), "{:?}", result);
}
