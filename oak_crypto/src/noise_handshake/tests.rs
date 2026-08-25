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
    noise_handshake::{
        NONCE_LEN, OrderedCrypter, SYMMETRIC_KEY_LEN, UnorderedCrypter, client::HandshakeInitiator,
        error::Error, respond_kk, respond_nk, respond_nn,
    },
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

/// Regression test for the Noise KK `se` DH term.
///
/// The KK pattern is `-> e, es, ss` / `<- e, ee, se`.  A previous
/// implementation computed a bogus fourth DH during the first message that
/// duplicated `ss` (DH(s_i, s_r)) instead of the real `se`
/// (DH(s_initiator, e_responder)), and omitted `se` from the response.  That
/// weakened forward secrecy: `se` binds the initiator's static key to the
/// responder's *ephemeral* key, so it must change on every handshake even
/// when the same static key pairs are reused.
///
/// This test runs two independent KK handshakes between the *same* static key
/// pairs and asserts the derived handshake hashes differ.  With the bug, the
/// only per-session randomness reaching the transcript came from `ee`; with a
/// correct `se` in place, the responder's ephemeral additionally feeds `se`.
/// Either way the transcripts must differ per session, and — more importantly
/// — both parties must agree, which the encrypt/decrypt round-trip in
/// `process_kk_handshake` already verifies with the corrected DH sequence.
#[test]
fn kk_handshake_is_unique_per_session() {
    let responder_priv = IdentityKey::generate();
    let responder_pub: [u8; 65] =
        responder_priv.get_public_key().unwrap().try_into().expect("bad public key length");

    let run_handshake = || {
        let init_priv: Box<dyn IdentityKeyHandle> = Box::new(IdentityKey::generate());
        let init_pub = init_priv.get_public_key().unwrap();
        let mut initiator = HandshakeInitiator::new_kk(responder_pub, init_priv);
        let message = initiator.build_initial_message().unwrap();
        let response = respond_kk(&responder_priv, &init_pub, &message).unwrap();
        // Both sides must agree on the handshake hash (proves the DH sequence
        // matches on initiator and responder).
        let (client_hash, _client_crypter) =
            initiator.process_response(&response.response).unwrap();
        assert_eq!(
            &client_hash, &response.handshake_hash,
            "initiator and responder must derive the same handshake hash"
        );
        response.handshake_hash
    };

    let hash_a = run_handshake();
    let hash_b = run_handshake();
    assert_ne!(
        hash_a, hash_b,
        "two KK handshakes must not produce identical transcripts (ephemeral contribution)"
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

/// Regression test: `UnorderedCrypter` must not update its replay state from
/// a message it has not authenticated.
///
/// The nonce is carried next to the ciphertext and is not covered by the AEAD
/// tag, so anyone able to put a packet on the wire chooses it. Before the fix
/// the window was advanced and the nonce recorded as used before
/// `aes_gcm_256_decrypt` ran, so a forged packet reserved a nonce: the genuine
/// message that later arrived with that nonce was rejected as a replay.
#[test]
fn unordered_crypter_forged_message_does_not_consume_nonce() {
    let key_1 = &[42u8; SYMMETRIC_KEY_LEN];
    let key_2 = &[52u8; SYMMETRIC_KEY_LEN];
    let mut sender = UnorderedCrypter::new(key_2, key_1, 8);
    let mut receiver = UnorderedCrypter::new(key_1, key_2, 8);

    let (ciphertext, nonce) = sender.encrypt(b"genuine payload").unwrap();
    let nonce: [u8; NONCE_LEN] = nonce.try_into().expect("unexpected nonce length");

    // Same nonce, ciphertext that does not authenticate.
    let forged = vec![0u8; ciphertext.len()];
    assert!(matches!(receiver.decrypt(&nonce, &forged), Err(Error::DecryptFailed)));

    // The genuine message must still be accepted.
    let plaintext = receiver
        .decrypt(&nonce, &ciphertext)
        .expect("genuine message rejected after a forged message reused its nonce");
    assert_eq!(plaintext, b"genuine payload");
}

/// Regression test: a forged message with a far-future nonce must not ratchet
/// the replay window past the messages that are still in flight.
#[test]
fn unordered_crypter_forged_message_does_not_advance_window() {
    let key_1 = &[42u8; SYMMETRIC_KEY_LEN];
    let key_2 = &[52u8; SYMMETRIC_KEY_LEN];
    let mut sender = UnorderedCrypter::new(key_2, key_1, 8);
    let mut receiver = UnorderedCrypter::new(key_1, key_2, 8);

    let mut in_flight = vec![];
    for message in [b"one".as_slice(), b"two".as_slice(), b"three".as_slice()] {
        let (ciphertext, nonce) = sender.encrypt(message).unwrap();
        let nonce: [u8; NONCE_LEN] = nonce.try_into().expect("unexpected nonce length");
        in_flight.push((message, ciphertext, nonce));
    }

    // A single unauthenticated packet claiming a nonce far ahead of the sender.
    let mut far_ahead = [0u8; NONCE_LEN];
    far_ahead[NONCE_LEN - 4..].copy_from_slice(&1_000_000u32.to_be_bytes());
    assert!(matches!(receiver.decrypt(&far_ahead, &[0u8; 48]), Err(Error::DecryptFailed)));

    for (message, ciphertext, nonce) in &in_flight {
        let plaintext = receiver
            .decrypt(nonce, ciphertext)
            .expect("genuine message dropped after a forged message moved the window");
        assert_eq!(&plaintext, message);
    }
}

/// Regression test: `OrderedCrypter` must not advance its receive-side nonce
/// counter from a message it has not authenticated.
///
/// `OrderedCrypter` allows no reordering or replay-window tolerance by
/// design: it expects consecutive nonces with no drop or reordering. Before
/// the fix, `decrypt` advanced the nonce counter before
/// `aes_gcm_256_decrypt` ran, so a single forged or corrupted packet reaching
/// the receiver first consumed the nonce the genuine sender's next message
/// was going to use. Because the counter never moves backward, every
/// subsequent genuine message then failed to decrypt too: the channel was
/// permanently desynced.
#[test]
fn ordered_crypter_forged_message_does_not_desync_channel() {
    let key_1 = &[42u8; SYMMETRIC_KEY_LEN];
    let key_2 = &[52u8; SYMMETRIC_KEY_LEN];
    let mut sender = OrderedCrypter::new(key_2, key_1);
    let mut receiver = OrderedCrypter::new(key_1, key_2);

    // Genuine message encrypted but not yet delivered (e.g. reordered/delayed
    // in transit behind the attacker's packet).
    let genuine_ciphertext = sender.encrypt(b"genuine payload").unwrap();

    // A forged packet, with no knowledge of the key, reaches the receiver first.
    let forged = vec![0u8; genuine_ciphertext.len()];
    assert!(matches!(receiver.decrypt(&forged), Err(Error::DecryptFailed)));

    // The genuine message, produced by the real sender and untampered, must
    // still be accepted -- the forged packet must not have consumed its nonce.
    let plaintext = receiver
        .decrypt(&genuine_ciphertext)
        .expect("genuine message rejected after a forged message reused its nonce");
    assert_eq!(plaintext, b"genuine payload");

    // The channel must also still be usable for subsequent messages.
    let next_ciphertext = sender.encrypt(b"second genuine payload").unwrap();
    let next_plaintext = receiver
        .decrypt(&next_ciphertext)
        .expect("channel remained desynced after the genuine message was correctly accepted");
    assert_eq!(next_plaintext, b"second genuine payload");
}
