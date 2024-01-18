//
// Copyright 2023 The Project Oak Authors
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

use alloc::{boxed::Box, sync::Arc, vec::Vec};

use anyhow::Context;
use async_trait::async_trait;

use crate::{
    encryptor::{
        AsyncEncryptionKeyHandle, AsyncServerEncryptor, ClientEncryptor,
        EncryptionKeyProvider, ServerEncryptor, OAK_HPKE_INFO,
    },
    hpke::{
        aead::{AEAD_ALGORITHM_KEY_SIZE_BYTES, AEAD_NONCE_SIZE_BYTES},
        generate_random_nonce, setup_base_recipient, setup_base_sender, KeyPair, RecipientContext,
    },
};

/// Test AES-GCM key that is only used in tests.
/// Was generated by calling [`Hpke::setup_base_sender`].
const TEST_AEAD_KEY: [u8; AEAD_ALGORITHM_KEY_SIZE_BYTES] = [
    11, 107, 5, 176, 4, 145, 171, 193, 163, 81, 105, 238, 171, 115, 56, 160, 130, 85, 22, 227, 118,
    76, 77, 89, 144, 223, 10, 112, 11, 149, 205, 199,
];
/// Test AES-GCM nonce that is only used in tests.
const TEST_NONCE: [u8; AEAD_NONCE_SIZE_BYTES] = [
    0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C,
];
const TEST_HPKE_INFO: &[u8] = b"Test HPKE info";
const TEST_REQUEST_MESSAGE: &[u8] = b"Test request message";
const TEST_REQUEST_ASSOCIATED_DATA: &[u8] = b"Test request associated data";
const TEST_RESPONSE_MESSAGE: &[u8] = b"Test response message";
const TEST_RESPONSE_ASSOCIATED_DATA: &[u8] = b"Test response associated data";

#[test]
fn test_aead() {
    let encrypted_message = crate::hpke::aead::encrypt(
        &TEST_AEAD_KEY,
        &TEST_NONCE,
        TEST_REQUEST_MESSAGE,
        TEST_REQUEST_ASSOCIATED_DATA,
    )
    .expect("couldn't encrypt test message");
    // Check that the message was encrypted.
    assert_ne!(TEST_REQUEST_MESSAGE, encrypted_message);
    let decrypted_message = crate::hpke::aead::decrypt(
        &TEST_AEAD_KEY,
        &TEST_NONCE,
        &encrypted_message,
        TEST_REQUEST_ASSOCIATED_DATA,
    )
    .expect("couldn't decrypt test message");
    // Test that AEAD decrypts message to the original one.
    assert_eq!(TEST_REQUEST_MESSAGE, decrypted_message);
}

#[test]
fn test_hpke() {
    let recipient_key_pair = KeyPair::generate();
    let (serialized_encapsulated_public_key, mut sender_context) = setup_base_sender(
        &recipient_key_pair.get_serialized_public_key(),
        TEST_HPKE_INFO,
    )
    .expect("couldn't setup base sender");
    let mut recipient_context = setup_base_recipient(
        &serialized_encapsulated_public_key,
        &recipient_key_pair,
        TEST_HPKE_INFO,
    )
    .expect("couldn't setup base recipient");

    let test_request_nonce = generate_random_nonce();
    let test_response_nonce = generate_random_nonce();

    let encrypted_request = sender_context
        .seal(
            &test_request_nonce,
            TEST_REQUEST_MESSAGE,
            TEST_REQUEST_ASSOCIATED_DATA,
        )
        .expect("sender context couldn't seal request");
    // Check that the message was encrypted.
    assert_ne!(TEST_REQUEST_MESSAGE, encrypted_request);
    let decrypted_request = recipient_context
        .open(
            &test_request_nonce,
            &encrypted_request,
            TEST_REQUEST_ASSOCIATED_DATA,
        )
        .expect("recipient context couldn't open request");
    assert_eq!(TEST_REQUEST_MESSAGE, decrypted_request);

    let encrypted_response = recipient_context
        .seal(
            &test_response_nonce,
            TEST_RESPONSE_MESSAGE,
            TEST_RESPONSE_ASSOCIATED_DATA,
        )
        .expect("recipient context couldn't seal response");
    // Check that the message was encrypted.
    assert_ne!(TEST_RESPONSE_MESSAGE, encrypted_response);
    let decrypted_response = sender_context
        .open(
            &test_response_nonce,
            &encrypted_response,
            TEST_RESPONSE_ASSOCIATED_DATA,
        )
        .expect("sender couldn't open response");
    assert_eq!(TEST_RESPONSE_MESSAGE, decrypted_response);
}

#[test]
fn test_encryptor() {
    let encryption_key = Arc::new(EncryptionKeyProvider::generate());
    let serialized_server_public_key = encryption_key.get_serialized_public_key();

    let mut client_encryptor = ClientEncryptor::create(&serialized_server_public_key)
        .expect("couldn't create client encryptor");
    let mut server_encryptor = None;

    let encrypted_request = client_encryptor
        .encrypt(TEST_REQUEST_MESSAGE, TEST_REQUEST_ASSOCIATED_DATA)
        .expect("client couldn't encrypt request");
    // Check that the message was encrypted.
    assert_ne!(
        TEST_REQUEST_MESSAGE,
        encrypted_request
            .encrypted_message
            .clone()
            .unwrap()
            .ciphertext
    );

    // Initialize server encryptor.
    if server_encryptor.is_none() {
        let serialized_encapsulated_public_key = encrypted_request
            .serialized_encapsulated_public_key
            .as_ref()
            .expect("initial request message doesn't contain encapsulated public key");
        server_encryptor = Some(
            ServerEncryptor::create(serialized_encapsulated_public_key, encryption_key.clone())
                .expect("couldn't create server encryptor"),
        );
    }

    let (decrypted_request, request_associated_data) = server_encryptor
        .as_mut()
        .expect("server encryptor is not initialized")
        .decrypt(&encrypted_request)
        .expect("server couldn't decrypt request");
    assert_eq!(TEST_REQUEST_MESSAGE, decrypted_request);
    assert_eq!(TEST_REQUEST_ASSOCIATED_DATA, request_associated_data);

    let encrypted_response = server_encryptor
        .as_mut()
        .expect("server encryptor is not initialized")
        .encrypt(TEST_RESPONSE_MESSAGE, TEST_RESPONSE_ASSOCIATED_DATA)
        .expect("server couldn't encrypt response");
    // Check that the message was encrypted.
    assert_ne!(
        TEST_RESPONSE_MESSAGE,
        encrypted_response
            .encrypted_message
            .clone()
            .unwrap()
            .ciphertext
    );
    let (decrypted_response, response_associated_data) = client_encryptor
        .decrypt(&encrypted_response)
        .expect("client couldn't decrypt response");
    assert_eq!(TEST_RESPONSE_MESSAGE, decrypted_response);
    assert_eq!(TEST_RESPONSE_ASSOCIATED_DATA, response_associated_data);
}

struct TestEncryptionKey {
    key_pair: KeyPair,
}

impl Default for TestEncryptionKey {
    fn default() -> Self {
        Self::new()
    }
}

impl TestEncryptionKey {
    pub fn new() -> Self {
        Self {
            key_pair: KeyPair::generate(),
        }
    }

    pub fn get_serialized_public_key(&self) -> Vec<u8> {
        self.key_pair.get_serialized_public_key()
    }
}

#[async_trait]
impl AsyncEncryptionKeyHandle for TestEncryptionKey {
    async fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        setup_base_recipient(encapsulated_public_key, &self.key_pair, OAK_HPKE_INFO)
            .context("couldn't generate recipient crypto context")
    }
}

#[tokio::test]
async fn test_async_encryptor() {
    let encryption_key = TestEncryptionKey::new();
    let serialized_server_public_key = encryption_key.get_serialized_public_key();

    let mut client_encryptor = ClientEncryptor::create(&serialized_server_public_key)
        .expect("couldn't create client encryptor");
    let mut server_encryptor = AsyncServerEncryptor::new(&encryption_key);

    let encrypted_request = client_encryptor
        .encrypt(TEST_REQUEST_MESSAGE, TEST_REQUEST_ASSOCIATED_DATA)
        .expect("client couldn't encrypt request");
    // Check that the message was encrypted.
    assert_ne!(
        TEST_REQUEST_MESSAGE,
        encrypted_request
            .encrypted_message
            .clone()
            .unwrap()
            .ciphertext
    );
    let (decrypted_request, request_associated_data) = server_encryptor
        .decrypt(&encrypted_request)
        .await
        .expect("server couldn't decrypt request");
    assert_eq!(TEST_REQUEST_MESSAGE, decrypted_request);
    assert_eq!(TEST_REQUEST_ASSOCIATED_DATA, request_associated_data);

    let encrypted_response = server_encryptor
        .encrypt(TEST_RESPONSE_MESSAGE, TEST_RESPONSE_ASSOCIATED_DATA)
        .expect("server couldn't encrypt response");
    // Check that the message was encrypted.
    assert_ne!(
        TEST_RESPONSE_MESSAGE,
        encrypted_response
            .encrypted_message
            .clone()
            .unwrap()
            .ciphertext
    );
    let (decrypted_response, response_associated_data) = client_encryptor
        .decrypt(&encrypted_response)
        .expect("client couldn't decrypt response");
    assert_eq!(TEST_RESPONSE_MESSAGE, decrypted_response);
    assert_eq!(TEST_RESPONSE_ASSOCIATED_DATA, response_associated_data);
}
