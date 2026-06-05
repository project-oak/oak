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

/// Regression test: the Noise KK `ss` step must use real ECDH, not a
/// SHA-256 hash of the two static public keys.
///
/// Before the fix, `ss` was computed as `SHA256(s_pub || rs_pub)` — a
/// value that is fully public and contributes zero private-key entropy to
/// the handshake.  As a result, any party that knows the two static public
/// keys can reproduce the `ss` mix and impersonate either endpoint without
/// possessing the corresponding private key.
///
/// This test demonstrates the correct property: completing a KK handshake
/// with a *wrong* initiator static key (one whose public key matches but
/// whose private key is different) must fail, not succeed.  Under the
/// buggy implementation both sides computed the same public-key hash so
/// the handshake still completed, making mutual authentication illusory.
#[test]
fn kk_handshake_rejects_wrong_initiator_static_key() {
    // Real responder key pair.
    let responder_priv = IdentityKey::generate();
    let responder_pub_bytes: [u8; 65] =
        responder_priv.get_public_key().unwrap().try_into().expect("unexpected public key length");

    // Legitimate initiator key pair.
    let legit_init_priv: Box<dyn IdentityKeyHandle> = Box::new(IdentityKey::generate());
    let legit_init_pub = legit_init_priv.get_public_key().unwrap();

    // Attacker key pair: different private key, but the attacker knows
    // legit_init_pub (it is public) and can construct an initiator message
    // that advertises legit_init_pub as its static key while actually using
    // a different private key for the DH operations.
    let attacker_priv: Box<dyn IdentityKeyHandle> = Box::new(IdentityKey::generate());

    // Build an initiator message using the *attacker*'s private key but
    // claiming legit_init_pub as the static identity.
    // With the buggy implementation (ss = SHA256(s_pub || rs_pub)) the
    // responder would accept this because ss does not bind to any private key.
    let mut attacker_initiator = HandshakeInitiator::new_kk(responder_pub_bytes, attacker_priv);
    let attacker_message = attacker_initiator.build_initial_message().unwrap();

    // The responder expects the initiator to hold legit_init_priv.
    // With the fix, the ss = ECDH(rs, s_i) step produces different key
    // material on each side, so decrypt_and_hash fails and respond_kk
    // returns Err.
    let result = respond_kk(&responder_priv, &legit_init_pub, &attacker_message);
    assert!(
        result.is_err(),
        "respond_kk must reject an initiator that does not hold the expected static private key"
    );
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
