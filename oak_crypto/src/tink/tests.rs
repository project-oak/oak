//
// Copyright 2025 Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use oak_crypto::verifier::Verifier;

use crate::signature_verifier::SignatureVerifier;

const MESSAGE_PATH: &str = "oak/cc/crypto/tink/signature/testdata/message";
const SIGNATURE_PATH: &str = "oak/cc/crypto/tink/signature/testdata/signature";
const KEYSET_PATH: &str = "oak/cc/crypto/tink/signature/testdata/public_keyset";

#[test]
fn test_signature_verifier_success() {
    // Read the message, signature, and public keyset.
    let message_file_path = format!("{}/{}", std::env::var("TEST_SRCDIR").unwrap(), MESSAGE_PATH);
    let message = std::fs::read(&message_file_path);
    assert!(message.is_ok());

    let signature_file_path =
        format!("{}/{}", std::env::var("TEST_SRCDIR").unwrap(), SIGNATURE_PATH);
    let signature = std::fs::read(&signature_file_path);
    assert!(signature.is_ok());

    let public_keyset_file_path =
        format!("{}/{}", std::env::var("TEST_SRCDIR").unwrap(), KEYSET_PATH);
    let public_keyset = std::fs::read(&public_keyset_file_path);
    assert!(public_keyset.is_ok());

    // Pass the variables to the SignatureVerifier function.
    let signature_verifier = SignatureVerifier::new(&public_keyset.unwrap());
    let result = signature_verifier.verify(&message.unwrap(), &signature.unwrap());

    assert!(result.is_ok());
}

#[test]
fn test_signature_verifier_fail() {
    // Read the message, signature, and public keyset.
    let message = "Some Unsigned Message";

    let signature_file_path =
        format!("{}/{}", std::env::var("TEST_SRCDIR").unwrap(), SIGNATURE_PATH);
    let signature = std::fs::read(&signature_file_path);
    assert!(signature.is_ok());

    let public_keyset_file_path =
        format!("{}/{}", std::env::var("TEST_SRCDIR").unwrap(), KEYSET_PATH);
    let public_keyset = std::fs::read(&public_keyset_file_path);
    assert!(public_keyset.is_ok());

    // Pass the variables to the SignatureVerifier function.
    let signature_verifier = SignatureVerifier::new(&public_keyset.unwrap());
    let result = signature_verifier.verify(message.as_bytes(), &signature.unwrap());

    assert!(result.is_err());
}
