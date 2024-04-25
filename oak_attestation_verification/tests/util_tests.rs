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
    convert_raw_to_verifying_key, equal_keys, get_hex_digest_match, looks_like_pem,
    verify_signature_raw, MatchResult,
};
use oak_proto_rust::oak::HexDigest;

const ENDORSEMENT_PATH: &str = "testdata/endorsement.json";
const ENDORSEMENT_SIGNATURE_PATH: &str = "testdata/endorsement.json.sig";
const ENDORSER_PUBLIC_KEY_PATH: &str = "testdata/oak_containers_stage1.pem";
const REKOR_PUBLIC_KEY_PATH: &str = "testdata/rekor_public_key.pem";

const HASH1: &str = "e27c682357589ac66bf06573da908469aeaeae5e73e4ecc525ac5d4b888822e7";
const HASH2: &str = "5649a7882a83a8c1c333db046fd0a60e9bacedb3caab3c91578a7e21b1da89e3";
const HASH3: &str = "536c56245ccee62530dd5febd49821ba4a6161c0";
const HASH4: &str = "fc5ed8a3ba1da6717da6031760a2deb45c52b836";

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

#[test]
fn test_both_empty_undecidable() {
    let empty = HexDigest { ..Default::default() };
    let result = get_hex_digest_match(&empty, &empty);
    assert!(result == MatchResult::UNDECIDABLE);
}

#[test]
fn test_one_empty_undecidable() {
    let a = HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
    let empty = HexDigest { ..Default::default() };
    let result = get_hex_digest_match(&a, &empty);
    assert!(result == MatchResult::UNDECIDABLE);
}

#[test]
fn test_same() {
    let a = HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
    let b = HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
    let result = get_hex_digest_match(&a, &b);
    assert!(result == MatchResult::SAME);
}

#[test]
fn test_different() {
    let a = HexDigest { sha2_256: HASH1.to_owned(), ..Default::default() };
    let b = HexDigest { sha2_256: HASH2.to_owned(), ..Default::default() };
    let result = get_hex_digest_match(&a, &b);
    assert!(result == MatchResult::DIFFERENT);
}

#[test]
fn test_contradictory() {
    let a = HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
    let b = HexDigest { sha1: HASH4.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
    let result = get_hex_digest_match(&a, &b);
    assert!(result == MatchResult::CONTRADICTORY);
}
