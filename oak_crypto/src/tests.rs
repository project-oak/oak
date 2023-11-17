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

use crate::{
    encryptor::{
        AsyncRecipientContextGenerator, AsyncServerEncryptor, ClientEncryptor,
        EncryptionKeyProvider, ServerEncryptor, OAK_HPKE_INFO,
    },
    hpke::{
        aead::{AEAD_ALGORITHM_KEY_SIZE_BYTES, AEAD_NONCE_SIZE_BYTES},
        setup_base_recipient, setup_base_sender, KeyPair, RecipientContext,
    },
    util::i2osp,
};
use alloc::{boxed::Box, sync::Arc, vec::Vec};
use anyhow::Context;
use async_trait::async_trait;

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
// Number of message exchanges done to test secure session handling.
const TEST_SESSION_SIZE: usize = 8;

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

    for i in 0..TEST_SESSION_SIZE {
        let test_request_message = [TEST_REQUEST_MESSAGE, &[i as u8]].concat();
        let test_request_associated_data = [TEST_REQUEST_ASSOCIATED_DATA, &[i as u8]].concat();
        let test_response_message = [TEST_RESPONSE_MESSAGE, &[i as u8]].concat();
        let test_response_associated_data = [TEST_RESPONSE_ASSOCIATED_DATA, &[i as u8]].concat();

        let encrypted_request = sender_context
            .seal(&test_request_message, &test_request_associated_data)
            .expect("sender context couldn't seal request");
        // Check that the message was encrypted.
        assert_ne!(test_request_message, encrypted_request);
        let decrypted_request = recipient_context
            .open(&encrypted_request, &test_request_associated_data)
            .expect("recipient context couldn't open request");
        assert_eq!(test_request_message, decrypted_request);

        let encrypted_response = recipient_context
            .seal(&test_response_message, &test_response_associated_data)
            .expect("recipient context couldn't seal response");
        // Check that the message was encrypted.
        assert_ne!(test_response_message, encrypted_response);
        let decrypted_response = sender_context
            .open(&encrypted_response, &test_response_associated_data)
            .expect("sender couldn't open response");
        assert_eq!(test_response_message, decrypted_response);
    }
}

#[test]
fn test_encryptor() {
    let key_provider = Arc::new(EncryptionKeyProvider::new());
    let serialized_server_public_key = key_provider.get_serialized_public_key();

    let mut client_encryptor = ClientEncryptor::create(&serialized_server_public_key)
        .expect("couldn't create client encryptor");
    let mut server_encryptor = None;

    for i in 0..TEST_SESSION_SIZE {
        let test_request_message = [TEST_REQUEST_MESSAGE, &[i as u8]].concat();
        let test_request_associated_data = [TEST_REQUEST_ASSOCIATED_DATA, &[i as u8]].concat();
        let test_response_message = [TEST_RESPONSE_MESSAGE, &[i as u8]].concat();
        let test_response_associated_data = [TEST_RESPONSE_ASSOCIATED_DATA, &[i as u8]].concat();

        let encrypted_request = client_encryptor
            .encrypt(&test_request_message, &test_request_associated_data)
            .expect("client couldn't encrypt request");
        // Check that the message was encrypted.
        assert_ne!(
            test_request_message,
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
                ServerEncryptor::create(serialized_encapsulated_public_key, key_provider.clone())
                    .expect("couldn't create server encryptor"),
            );
        }

        let (decrypted_request, request_associated_data) = server_encryptor
            .as_mut()
            .expect("server encryptor is not initialized")
            .decrypt(&encrypted_request)
            .expect("server couldn't decrypt request");
        assert_eq!(test_request_message, decrypted_request);
        assert_eq!(test_request_associated_data, request_associated_data);

        let encrypted_response = server_encryptor
            .as_mut()
            .expect("server encryptor is not initialized")
            .encrypt(&test_response_message, &test_response_associated_data)
            .expect("server couldn't encrypt response");
        // Check that the message was encrypted.
        assert_ne!(
            test_response_message,
            encrypted_response
                .encrypted_message
                .clone()
                .unwrap()
                .ciphertext
        );
        let (decrypted_response, response_associated_data) = client_encryptor
            .decrypt(&encrypted_response)
            .expect("client couldn't decrypt response");
        assert_eq!(test_response_message, decrypted_response);
        assert_eq!(test_response_associated_data, response_associated_data);
    }
}

struct TestEncryptionKeyProvider {
    key_pair: KeyPair,
}

impl Default for TestEncryptionKeyProvider {
    fn default() -> Self {
        Self::new()
    }
}

impl TestEncryptionKeyProvider {
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
impl AsyncRecipientContextGenerator for TestEncryptionKeyProvider {
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
    let key_provider = TestEncryptionKeyProvider::new();
    let serialized_server_public_key = key_provider.get_serialized_public_key();

    let mut client_encryptor = ClientEncryptor::create(&serialized_server_public_key)
        .expect("couldn't create client encryptor");
    let mut server_encryptor = AsyncServerEncryptor::new(&key_provider);

    for i in 0..TEST_SESSION_SIZE {
        let test_request_message = [TEST_REQUEST_MESSAGE, &[i as u8]].concat();
        let test_request_associated_data = [TEST_REQUEST_ASSOCIATED_DATA, &[i as u8]].concat();
        let test_response_message = [TEST_RESPONSE_MESSAGE, &[i as u8]].concat();
        let test_response_associated_data = [TEST_RESPONSE_ASSOCIATED_DATA, &[i as u8]].concat();

        let encrypted_request = client_encryptor
            .encrypt(&test_request_message, &test_request_associated_data)
            .expect("client couldn't encrypt request");
        // Check that the message was encrypted.
        assert_ne!(
            test_request_message,
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
        assert_eq!(test_request_message, decrypted_request);
        assert_eq!(test_request_associated_data, request_associated_data);

        let encrypted_response = server_encryptor
            .encrypt(&test_response_message, &test_response_associated_data)
            .expect("server couldn't encrypt response");
        // Check that the message was encrypted.
        assert_ne!(
            test_response_message,
            encrypted_response
                .encrypted_message
                .clone()
                .unwrap()
                .ciphertext
        );
        let (decrypted_response, response_associated_data) = client_encryptor
            .decrypt(&encrypted_response)
            .expect("client couldn't decrypt response");
        assert_eq!(test_response_message, decrypted_response);
        assert_eq!(test_response_associated_data, response_associated_data);
    }
}

#[test]
fn test_i2osp() {
    assert_eq!(i2osp::<4>(0x1000).unwrap(), [0x00, 0x00, 0x10, 0x00]);
    assert_eq!(i2osp::<4>(0x123).unwrap(), [0x00, 0x00, 0x01, 0x23]);
    assert_eq!(i2osp::<3>(0x12345).unwrap(), [0x01, 0x23, 0x45]);
    assert!(i2osp::<1>(0x123).is_err());
}
