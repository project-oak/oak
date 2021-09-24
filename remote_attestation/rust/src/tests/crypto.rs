//
// Copyright 2021 The Project Oak Authors
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

use crate::{
    crypto::{
        get_sha256, AeadEncryptor, DecryptionKey, EncryptionKey, KeyNegotiator, KeyNegotiatorType,
        SignatureVerifier, Signer, AEAD_ALGORITHM_KEY_LENGTH, CLIENT_KEY_PURPOSE,
        KEY_AGREEMENT_ALGORITHM_KEY_LENGTH, NONCE_LENGTH, SERVER_KEY_PURPOSE, SHA256_HASH_LENGTH,
        SIGNATURE_LENGTH, SIGNING_ALGORITHM_KEY_LENGTH,
    },
    message::EncryptedData,
};
use quickcheck_macros::quickcheck;

// Keys are only used for test purposes.
// Were created by printing out values in the `crate::crypto` using `println!`.
const KEY_MATERIAL: [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH] = [
    60, 42, 197, 238, 121, 136, 107, 43, 1, 207, 63, 140, 212, 12, 2, 188, 56, 164, 115, 88, 78,
    61, 160, 69, 12, 131, 187, 250, 173, 18, 146, 23,
];
const SERVER_KEY_AGREEMENT_PUBLIC_KEY: [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH] = [
    159, 12, 61, 172, 239, 0, 129, 205, 167, 250, 118, 50, 23, 39, 135, 72, 68, 139, 125, 122, 145,
    224, 155, 20, 42, 98, 211, 28, 67, 125, 47, 68,
];
const CLIENT_KEY_AGREEMENT_PUBLIC_KEY: [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH] = [
    75, 130, 163, 244, 38, 189, 249, 222, 43, 127, 116, 150, 233, 190, 243, 236, 19, 237, 74, 108,
    9, 122, 105, 223, 34, 125, 125, 242, 239, 66, 78, 95,
];
const SERVER_ENCRYPTION_KEY: [u8; AEAD_ALGORITHM_KEY_LENGTH] = [
    148, 3, 161, 94, 41, 6, 250, 223, 92, 22, 86, 91, 150, 171, 248, 51, 221, 90, 230, 90, 151, 55,
    59, 108, 21, 54, 33, 61, 219, 140, 229, 59,
];
const CLIENT_ENCRYPTION_KEY: [u8; AEAD_ALGORITHM_KEY_LENGTH] = [
    48, 90, 139, 218, 156, 196, 174, 129, 15, 178, 216, 181, 106, 232, 160, 188, 136, 103, 87, 120,
    231, 20, 78, 129, 237, 225, 173, 25, 179, 152, 139, 82,
];
const SIGNING_PUBLIC_KEY: [u8; SIGNING_ALGORITHM_KEY_LENGTH] = [
    4, 51, 234, 203, 59, 199, 24, 233, 70, 68, 246, 116, 56, 113, 159, 19, 252, 238, 243, 127, 133,
    116, 177, 172, 54, 42, 233, 123, 233, 25, 181, 153, 133, 63, 45, 191, 156, 46, 102, 156, 93,
    183, 74, 48, 189, 37, 49, 50, 66, 90, 61, 100, 2, 81, 180, 225, 13, 253, 220, 7, 54, 127, 13,
    131, 85,
];

const DATA: [u8; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
// [`DATA`] encrypted with [`CLIENT_ENCRYPTION_KEY`],
const ENCRYPTED_DATA: [u8; 26] = [
    255, 242, 249, 3, 114, 107, 147, 122, 38, 153, 12, 33, 62, 56, 172, 90, 234, 207, 50, 219, 22,
    212, 169, 40, 113, 28,
];
const INVALID_ENCRYPTED_DATA: [u8; 26] = [0; 26];
const ENCRYPTED_DATA_NONCE: [u8; NONCE_LENGTH] =
    [106, 176, 114, 112, 226, 142, 211, 123, 95, 187, 120, 206];
const INVALID_ENCRYPTED_DATA_NONCE: [u8; NONCE_LENGTH] = [0; NONCE_LENGTH];
const DATA_SIGNATURE: [u8; SIGNATURE_LENGTH] = [
    14, 133, 10, 201, 218, 60, 123, 206, 59, 25, 101, 172, 89, 65, 201, 197, 92, 249, 247, 99, 133,
    8, 217, 94, 125, 160, 31, 141, 61, 197, 119, 2, 41, 79, 195, 23, 105, 0, 50, 253, 111, 103, 19,
    188, 169, 243, 11, 157, 49, 155, 154, 249, 14, 29, 183, 167, 0, 82, 74, 74, 221, 214, 250, 222,
];
const INVALID_DATA_SIGNATURE: [u8; SIGNATURE_LENGTH] = [0; SIGNATURE_LENGTH];
const DATA_SHA256_HASH: [u8; SHA256_HASH_LENGTH] = [
    31, 130, 90, 162, 240, 2, 14, 247, 207, 145, 223, 163, 13, 164, 102, 141, 121, 28, 93, 72, 36,
    252, 142, 65, 53, 75, 137, 236, 5, 121, 90, 179,
];

#[test]
fn test_decrypt() {
    let mut encryptor = AeadEncryptor::new(
        EncryptionKey(SERVER_ENCRYPTION_KEY),
        DecryptionKey(CLIENT_ENCRYPTION_KEY),
    );
    let result = encryptor.decrypt(&EncryptedData::new(
        ENCRYPTED_DATA_NONCE,
        ENCRYPTED_DATA.to_vec(),
    ));
    assert_eq!(result.unwrap(), DATA);

    let result = encryptor.decrypt(&EncryptedData::new(
        INVALID_ENCRYPTED_DATA_NONCE,
        ENCRYPTED_DATA.to_vec(),
    ));
    assert!(result.is_err());
    let result = encryptor.decrypt(&EncryptedData::new(
        ENCRYPTED_DATA_NONCE,
        INVALID_ENCRYPTED_DATA.to_vec(),
    ));
    assert!(result.is_err());
}

#[quickcheck]
fn test_encrypt(data: Vec<u8>) -> bool {
    let mut server_encryptor = AeadEncryptor::new(
        EncryptionKey(SERVER_ENCRYPTION_KEY),
        DecryptionKey(CLIENT_ENCRYPTION_KEY),
    );
    let mut client_encryptor = AeadEncryptor::new(
        EncryptionKey(CLIENT_ENCRYPTION_KEY),
        DecryptionKey(SERVER_ENCRYPTION_KEY),
    );

    let encrypted_data = server_encryptor
        .encrypt(&data)
        .expect("Couldn't encrypt data");
    let decrypted_data = client_encryptor
        .decrypt(&encrypted_data)
        .expect("Couldn't decrypt data");
    data == decrypted_data
}

#[test]
fn test_create_key_negotiator() {
    let server_key_negotiator = KeyNegotiator::create(KeyNegotiatorType::Server)
        .expect("Couldn't create server key negotiator");
    let client_key_negotiator = KeyNegotiator::create(KeyNegotiatorType::Client)
        .expect("Couldn't create client key negotiator");

    let server_ephemeral_public_key = server_key_negotiator.public_key();
    assert!(server_ephemeral_public_key.is_ok());
    let client_ephemeral_public_key = client_key_negotiator.public_key();
    assert!(client_ephemeral_public_key.is_ok());
}

#[test]
fn test_key_derivation_function() {
    let server_encryption_key = KeyNegotiator::key_derivation_function(
        &KEY_MATERIAL,
        SERVER_KEY_PURPOSE,
        &SERVER_KEY_AGREEMENT_PUBLIC_KEY,
        &CLIENT_KEY_AGREEMENT_PUBLIC_KEY,
    );
    assert!(server_encryption_key.is_ok());
    assert_eq!(server_encryption_key.unwrap(), SERVER_ENCRYPTION_KEY);

    let client_encryption_key = KeyNegotiator::key_derivation_function(
        &KEY_MATERIAL,
        CLIENT_KEY_PURPOSE,
        &SERVER_KEY_AGREEMENT_PUBLIC_KEY,
        &CLIENT_KEY_AGREEMENT_PUBLIC_KEY,
    );
    assert!(client_encryption_key.is_ok());
    assert_eq!(client_encryption_key.unwrap(), CLIENT_ENCRYPTION_KEY);
}

#[test]
fn test_derive_session_keys() {
    let server_key_negotiator = KeyNegotiator::create(KeyNegotiatorType::Server).unwrap();
    let client_key_negotiator = KeyNegotiator::create(KeyNegotiatorType::Client).unwrap();

    let server_ephemeral_public_key = server_key_negotiator.public_key().unwrap();
    let client_ephemeral_public_key = client_key_negotiator.public_key().unwrap();

    let result = server_key_negotiator.derive_session_keys(&client_ephemeral_public_key);
    assert!(result.is_ok());
    let (server_encryption_key, server_decryption_key) = result.unwrap();

    let result = client_key_negotiator.derive_session_keys(&server_ephemeral_public_key);
    assert!(result.is_ok());
    let (client_encryption_key, client_decryption_key) = result.unwrap();

    assert_eq!(server_encryption_key.0, client_decryption_key.0);
    assert_eq!(server_decryption_key.0, client_encryption_key.0);
}

#[test]
fn test_create_encryptor() {
    let server_key_negotiator = KeyNegotiator::create(KeyNegotiatorType::Server).unwrap();
    let client_key_negotiator = KeyNegotiator::create(KeyNegotiatorType::Client).unwrap();

    let server_ephemeral_public_key = server_key_negotiator.public_key().unwrap();
    let client_ephemeral_public_key = client_key_negotiator.public_key().unwrap();

    let mut server_encryptor = server_key_negotiator
        .create_encryptor(&client_ephemeral_public_key)
        .expect("Couldn't create server encryptor");
    let mut client_encryptor = client_key_negotiator
        .create_encryptor(&server_ephemeral_public_key)
        .expect("Couldn't create client encryptor");

    let encrypted_server_data = server_encryptor.encrypt(&DATA).unwrap();
    let decrypted_server_data = client_encryptor.decrypt(&encrypted_server_data).unwrap();
    assert_eq!(decrypted_server_data, DATA);

    let encrypted_client_data = client_encryptor.encrypt(&DATA).unwrap();
    let decrypted_client_data = server_encryptor.decrypt(&encrypted_client_data).unwrap();
    assert_eq!(decrypted_client_data, DATA);
}

#[test]
fn test_create_signer() {
    let signer = Signer::create().expect("Couldn't create signer");
    let result = signer.public_key();
    assert!(result.is_ok());
}

#[test]
fn test_verify() {
    let verifier = SignatureVerifier::new(&SIGNING_PUBLIC_KEY);
    let result = verifier.verify(&DATA, &DATA_SIGNATURE);
    assert!(result.is_ok());
    let result = verifier.verify(&DATA, &INVALID_DATA_SIGNATURE);
    assert!(result.is_err());
}

#[quickcheck]
fn test_sign(data: Vec<u8>) -> bool {
    let signer = Signer::create().expect("Couldn't create signer");
    let public_key = signer
        .public_key()
        .expect("Couldn't get signing public key");
    let signature = signer.sign(&data).expect("Couldn't sign data");

    let verifier = SignatureVerifier::new(&public_key);
    let result = verifier.verify(&data, &signature);
    result.is_ok()
}

#[test]
fn test_get_sha256() {
    let test_hash = get_sha256(&DATA);
    assert_eq!(test_hash, DATA_SHA256_HASH);
}
