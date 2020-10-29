//
// Copyright 2020 The Project Oak Authors
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

use assert_matches::assert_matches;
use oak_sign::{get_sha256_hex, KeyPair, SignatureBundle};

const TEST_DATA: &str = "Test data";
const TEST_SHA256: &str = "e27c8214be8b7cf5bccc7c08247e3cb0c1514a48ee1f63197fe4ef3ef51d7e6f";
const INCORRECT_SIGNATURE: &str =
    "JmtVw8SPMnU/f4fLSBvd+w96C2NAMFn7+rqGVHzWOItsdZ+T+TqBwnEcCNJrJ1wrQWXPwFk+8sRiRFFCOCJVAA==";

#[test]
fn key_pair_serialization_deserialization_test() {
    let generate_result = KeyPair::generate();
    assert_matches!(generate_result, Ok(_));
    let key_pair = generate_result.unwrap();

    let pkcs8_key_pair = key_pair.pkcs8_key_pair();
    let parse_result = KeyPair::parse(&pkcs8_key_pair);
    assert_matches!(parse_result, Ok(_));
    let parsed_key_pair = parse_result.unwrap();

    assert_eq!(key_pair, parsed_key_pair);
}

#[test]
fn signature_test() {
    let key_pair = KeyPair::generate().expect("Couldn't create key pair");
    let create_result = SignatureBundle::create(TEST_DATA.as_bytes(), &key_pair);
    assert_matches!(create_result, Ok(_));
    let signature = create_result.unwrap();

    let verify_result = signature.verify();
    assert_matches!(verify_result, Ok(_));

    let incorrect_signature = SignatureBundle {
        public_key: signature.public_key.to_vec(),
        signed_hash: INCORRECT_SIGNATURE.as_bytes().to_vec(),
        hash: signature.signed_hash.to_vec(),
    };
    let incorrect_verify_result = incorrect_signature.verify();
    assert_matches!(incorrect_verify_result, Err(_));
}

#[test]
fn sha256_test() {
    let hash = get_sha256_hex(TEST_DATA.as_bytes());
    assert_eq!(hash, TEST_SHA256);
}
