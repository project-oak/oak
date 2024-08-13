// Copyright 2024 Oak Authors
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

#[cfg(test)]
use alloc::{boxed::Box, vec};

use crate::{
    identity_key::{IdentityKey, IdentityKeyHandle},
    noise_handshake::{client::HandshakeInitiator, respond_kk, respond_nk, respond_nn},
};

#[test]
fn process_kk_handshake() {
    let test_messages = vec![vec![1u8, 2u8, 3u8, 4u8], vec![4u8, 3u8, 2u8, 1u8], vec![]];
    let identity_priv = IdentityKey::generate();
    let identity_pub_bytes = identity_priv
        .get_public_key()
        .expect("couldn't get the public key from the generated identity key");
    let init_priv: Box<dyn IdentityKeyHandle> = Box::new(IdentityKey::generate());
    let init_pub = init_priv.get_public_key().unwrap();
    let mut initiator =
        HandshakeInitiator::new_kk(identity_pub_bytes.try_into().unwrap(), init_priv);
    let message = initiator.build_initial_message().unwrap();
    let handshake_response = respond_kk(&identity_priv, &init_pub, &message).unwrap();
    let mut enclave_crypter = handshake_response.crypter;

    let (client_hash, mut client_crypter) =
        initiator.process_response(&handshake_response.response).unwrap();
    assert_eq!(&client_hash, &handshake_response.handshake_hash);

    // Client -> Enclave encrypt+decrypt
    for message in &test_messages {
        let ciphertext = client_crypter.encrypt(message).unwrap();
        let plaintext = enclave_crypter.decrypt(&ciphertext).unwrap();
        assert_eq!(message, &plaintext);
    }

    // Enclave -> Client encrypt+decrypt
    for message in &test_messages {
        let ciphertext = enclave_crypter.encrypt(message).unwrap();
        let plaintext = client_crypter.decrypt(&ciphertext).unwrap();
        assert_eq!(message, &plaintext);
    }
}

#[test]
fn process_nk_handshake() {
    let test_messages = vec![vec![1u8, 2u8, 3u8, 4u8], vec![4u8, 3u8, 2u8, 1u8], vec![]];
    let identity_priv = IdentityKey::generate();
    let identity_pub_bytes = identity_priv
        .get_public_key()
        .expect("couldn't get the public key from the generated identity key");
    let mut initiator = HandshakeInitiator::new_nk(
        identity_pub_bytes.as_slice().try_into().expect("wrong public key format"),
    );
    let message = initiator.build_initial_message().unwrap();
    let handshake_response = respond_nk(&identity_priv, &message).unwrap();
    let mut enclave_crypter = handshake_response.crypter;

    let (client_hash, mut client_crypter) =
        initiator.process_response(&handshake_response.response).unwrap();
    assert_eq!(&client_hash, &handshake_response.handshake_hash);

    // Client -> Enclave encrypt+decrypt
    for message in &test_messages {
        let ciphertext = client_crypter.encrypt(message).unwrap();
        let plaintext = enclave_crypter.decrypt(&ciphertext).unwrap();
        assert_eq!(message, &plaintext);
    }

    // Enclave -> Client encrypt+decrypt
    for message in &test_messages {
        let ciphertext = enclave_crypter.encrypt(message).unwrap();
        let plaintext = client_crypter.decrypt(&ciphertext).unwrap();
        assert_eq!(message, &plaintext);
    }
}

#[test]
fn process_nn_handshake() {
    let test_messages = vec![vec![1u8, 2u8, 3u8, 4u8], vec![4u8, 3u8, 2u8, 1u8], vec![]];
    let mut initiator = HandshakeInitiator::new_nn();
    let message = initiator.build_initial_message().unwrap();
    let handshake_response = respond_nn(&message).unwrap();
    let mut enclave_crypter = handshake_response.crypter;

    let (client_hash, mut client_crypter) =
        initiator.process_response(&handshake_response.response).unwrap();
    assert_eq!(&client_hash, &handshake_response.handshake_hash);

    // Client -> Enclave encrypt+decrypt
    for message in &test_messages {
        let ciphertext = client_crypter.encrypt(message).unwrap();
        let plaintext = enclave_crypter.decrypt(&ciphertext).unwrap();
        assert_eq!(message, &plaintext);
    }

    // Enclave -> Client encrypt+decrypt
    for message in &test_messages {
        let ciphertext = enclave_crypter.encrypt(message).unwrap();
        let plaintext = client_crypter.decrypt(&ciphertext).unwrap();
        assert_eq!(message, &plaintext);
    }
}
