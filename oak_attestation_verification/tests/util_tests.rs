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

use oak_attestation_verification::util::{
    convert_pem_to_raw, convert_pem_to_verifying_key, convert_raw_to_pem,
    convert_raw_to_verifying_key, equal_keys, looks_like_pem, verify_signature_raw,
};

const ENDORSEMENT_PATH: &str = "testdata/endorsement.json";
const ENDORSEMENT_SIGNATURE_PATH: &str = "testdata/endorsement.json.sig";
const ENDORSER_PUBLIC_KEY_PATH: &str = "testdata/oak_containers_stage1.pem";
const REKOR_PUBLIC_KEY_PATH: &str = "testdata/rekor_public_key.pem";

struct TestData {
    endorsement: Vec<u8>,
    endorsement_signature: Vec<u8>,
    endorser_public_key_pem: String,
    rekor_public_key_pem: String,
    endorser_public_key: Vec<u8>,
    rekor_public_key: Vec<u8>,
}

fn load_testdata() -> TestData {
    let endorsement = fs::read(ENDORSEMENT_PATH).expect("couldn't read endorsement");
    let endorsement_signature =
        fs::read(ENDORSEMENT_SIGNATURE_PATH).expect("couldn't read endorsement");
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
        endorsement_signature,
        endorser_public_key_pem,
        rekor_public_key_pem,
        endorser_public_key,
        rekor_public_key,
    }
}

#[test]
fn test_looks_like_pem() {
    let testdata = load_testdata();
    assert!(looks_like_pem(&testdata.endorser_public_key_pem));
    assert!(looks_like_pem(&testdata.rekor_public_key_pem));
    assert!(!looks_like_pem("-----BEGIN PUBLIC KEY-----\n"));
    assert!(!looks_like_pem("\n-----END PUBLIC KEY-----\n"));
    assert!(!looks_like_pem("whatever"));
}

#[test]
fn test_convert_from_pem() {
    let testdata = load_testdata();
    let key = convert_pem_to_verifying_key(&testdata.rekor_public_key_pem);
    assert!(key.is_ok());
}

#[test]
fn test_convert_from_raw() {
    let testdata = load_testdata();
    let key = convert_raw_to_verifying_key(&testdata.rekor_public_key);
    assert!(key.is_ok());
}

#[test]
fn test_convert_inverse_left() {
    let testdata = load_testdata();
    let pem = convert_raw_to_pem(&testdata.rekor_public_key);
    let actual = convert_pem_to_raw(&pem).expect("could not convert key");
    assert!(
        equal_keys(&testdata.rekor_public_key, &actual).expect("could not compare keys"),
        "{:?}",
        pem
    );
}

#[test]
fn test_convert_inverse_right() {
    let testdata = load_testdata();
    let raw = convert_pem_to_raw(&testdata.rekor_public_key_pem).expect("could not convert key");
    let actual = convert_raw_to_pem(&raw);
    assert!(
        actual.eq(&testdata.rekor_public_key_pem),
        "expected: {:?} actual: {:?}",
        &testdata.rekor_public_key_pem,
        actual
    );
}

#[test]
fn test_verify_signature() {
    let testdata = load_testdata();
    let result = verify_signature_raw(
        &testdata.endorsement_signature,
        &testdata.endorsement,
        &testdata.endorser_public_key,
    );
    assert!(result.is_ok());
}
