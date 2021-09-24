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
use oak_sign::{
    decode_public_key_der, encode_public_key_der, get_sha256_hex, KeyPair, SignatureBundle,
};

const DATA: &str = "Test data";
const TEST_SHA256: &str = "e27c8214be8b7cf5bccc7c08247e3cb0c1514a48ee1f63197fe4ef3ef51d7e6f";
const INCORRECT_SIGNATURE: &str =
    "JmtVw8SPMnU/f4fLSBvd+w96C2NAMFn7+rqGVHzWOItsdZ+T+TqBwnEcCNJrJ1wrQWXPwFk+8sRiRFFCOCJVAA==";

#[test]
fn key_pair_serialization_deserialization_test() {
    let generate_result = KeyPair::generate();
    assert_matches!(generate_result, Ok(_));
    let key_pair = generate_result.unwrap();

    let key_pair_pkcs_8 = key_pair.key_pair_pkcs_8();
    let parse_result = KeyPair::parse(&key_pair_pkcs_8);
    assert_matches!(parse_result, Ok(_));
    let parsed_key_pair = parse_result.unwrap();

    assert_eq!(key_pair, parsed_key_pair);
}

#[test]
fn signature_test() {
    let key_pair = KeyPair::generate().expect("Couldn't create key pair");
    let create_result = SignatureBundle::create(DATA.as_bytes(), &key_pair);
    assert_matches!(create_result, Ok(_));
    let signature = create_result.unwrap();

    let verify_result = signature.verify();
    assert_matches!(verify_result, Ok(_));

    let incorrect_signature = SignatureBundle {
        public_key_der: signature.public_key_der.clone(),
        signed_hash: INCORRECT_SIGNATURE.as_bytes().to_vec(),
        hash: signature.signed_hash,
    };
    let incorrect_verify_result = incorrect_signature.verify();
    assert_matches!(incorrect_verify_result, Err(_));
}

#[test]
fn public_key_der_encode_decode() {
    // Ground truth: https://gchq.github.io/CyberChef/#recipe=Parse_ASN.1_hex_string(0,32)&input=MzAyYTMwMDUwNjAzMmI2NTcwMDMyMTAwN2Y4ZDUyMGE1MzZkNDc4OGI4ZWFmZDkzYmExZDVmNDBiNmVkZmQ5YTkxYWY1OTQ0MzVhOGMyNWJkZGEzYzhmZQ
    const PUBLIC_KEY_DER_HEX: &str =
        "302a300506032b65700321007f8d520a536d4788b8eafd93ba1d5f40b6edfd9a91af594435a8c25bdda3c8fe";
    const PUBLIC_KEY_RAW_HEX: &str =
        "7f8d520a536d4788b8eafd93ba1d5f40b6edfd9a91af594435a8c25bdda3c8fe";
    assert_eq!(
        hex::decode(PUBLIC_KEY_DER_HEX).unwrap(),
        encode_public_key_der(&hex::decode(PUBLIC_KEY_RAW_HEX).unwrap()).unwrap()
    );
    assert_eq!(
        hex::decode(PUBLIC_KEY_RAW_HEX).unwrap(),
        decode_public_key_der(&hex::decode(PUBLIC_KEY_DER_HEX).unwrap()).unwrap()
    );
}

#[test]
fn sha256_test() {
    let hash = get_sha256_hex(DATA.as_bytes());
    assert_eq!(hash, TEST_SHA256);
}
