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
use oak_file_utils::data_path;

use crate::{alloc::string::ToString, signature_verifier::SignatureVerifier};

const MESSAGE_PATH: &str = "cc/crypto/tink/signature/testdata/message";
const SIGNATURE_PATH: &str = "cc/crypto/tink/signature/testdata/signature";
const KEYSET_PATH: &str = "cc/crypto/tink/signature/testdata/public_keyset";

#[test]
fn test_signature_verifier_success() {
    // Read the message, signature, and public keyset.
    let message = std::fs::read(data_path(MESSAGE_PATH));
    assert!(message.is_ok());

    let signature = std::fs::read(data_path(SIGNATURE_PATH));
    assert!(signature.is_ok());

    let public_keyset = std::fs::read(data_path(KEYSET_PATH));
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

    let signature = std::fs::read(data_path(SIGNATURE_PATH));
    assert!(signature.is_ok());

    let public_keyset = std::fs::read(data_path(KEYSET_PATH));
    assert!(public_keyset.is_ok());

    // Pass the variables to the SignatureVerifier function.
    let signature_verifier = SignatureVerifier::new(&public_keyset.unwrap());
    let result = signature_verifier.verify(message.as_bytes(), &signature.unwrap());

    assert!(result.is_err());
}

// ── ML-DSA-44 round-trip tests ────────────────────────────────────────

use crate::ml_dsa_44;

#[test]
fn ml_dsa_44_sign_and_verify_round_trip() {
    let key_pair = ml_dsa_44::generate_key_pair().unwrap();

    let message = b"test message for ML-DSA-44 round trip";
    let signature = key_pair.sign(message).unwrap();

    assert_eq!(signature.as_ref().len(), ml_dsa_44::SIGNATURE_BYTES);
    assert!(key_pair.verifying_key().verify(message, &signature));
}

#[test]
fn ml_dsa_44_verify_rejects_wrong_message() {
    let key_pair = ml_dsa_44::generate_key_pair().unwrap();

    let signature = key_pair.sign(b"original message").unwrap();

    assert!(!key_pair.verifying_key().verify(b"different message", &signature));
}

#[test]
fn ml_dsa_44_verify_rejects_wrong_key() {
    let key_pair_1 = ml_dsa_44::generate_key_pair().unwrap();
    let key_pair_2 = ml_dsa_44::generate_key_pair().unwrap();

    let signature = key_pair_1.sign(b"signed by key_pair_1").unwrap();

    assert!(!key_pair_2.verifying_key().verify(b"signed by key_pair_1", &signature));
}

#[test]
fn ml_dsa_44_keygen_produces_valid_key_lengths() {
    let key_pair = ml_dsa_44::generate_key_pair().unwrap();

    assert_eq!(key_pair.verifying_key().as_ref().len(), ml_dsa_44::PUBLIC_KEY_BYTES);
}

#[test]
fn ml_dsa_44_two_key_pairs_are_different() {
    let key_pair_1 = ml_dsa_44::generate_key_pair().unwrap();
    let key_pair_2 = ml_dsa_44::generate_key_pair().unwrap();

    assert_ne!(key_pair_1.verifying_key(), key_pair_2.verifying_key());
}

#[test]
fn ml_dsa_44_verifying_key_rejects_invalid_length() {
    let err = ml_dsa_44::VerifyingKey::try_from(&[0u8; 10][..]).unwrap_err();
    assert!(err.to_string().contains("invalid public key length"), "unexpected error: {err}");
}

#[test]
fn ml_dsa_44_signature_rejects_invalid_length() {
    let err = ml_dsa_44::Signature::try_from(&[0u8; 10][..]).unwrap_err();
    assert!(err.to_string().contains("invalid signature length"), "unexpected error: {err}");
}
