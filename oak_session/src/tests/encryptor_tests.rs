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

use std::vec::Vec;

use googletest::prelude::*;
use oak_crypto::{
    encryptor::{Encryptor, Payload},
    noise_handshake::{SYMMETRIC_KEY_LEN, UnorderedCrypter},
};
use oak_proto_rust::oak::session::v1::PlaintextMessage;
use oak_session::encryptors::UnorderedChannelEncryptor;

fn test_messages() -> Vec<PlaintextMessage> {
    vec![
        PlaintextMessage { plaintext: vec![1u8, 2u8, 3u8, 4u8] },
        PlaintextMessage { plaintext: vec![4u8, 3u8, 2u8, 1u8] },
        PlaintextMessage { plaintext: vec![] },
    ]
}

#[test]
fn test_unordered_encryptor_inorder_messages() {
    let key_1 = &[42u8; SYMMETRIC_KEY_LEN];
    let key_2 = &[52u8; SYMMETRIC_KEY_LEN];
    let mut replica_1 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_1, key_2, 0) };
    let mut replica_2 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_2, key_1, 0) };
    for message in test_messages() {
        let payload = Payload { message: message.plaintext.to_vec(), nonce: None, aad: None };
        let encrypted_payload = replica_1.encrypt(payload).unwrap();
        let plaintext = replica_2.decrypt(encrypted_payload).unwrap().message;
        assert_that!(message.plaintext, eq(&plaintext));
    }
}

#[test]
fn test_unordered_encryptor_handles_missing_nonce_on_decrypt() {
    let key_1 = &[42u8; SYMMETRIC_KEY_LEN];
    let key_2 = &[52u8; SYMMETRIC_KEY_LEN];
    let mut replica_1 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_1, key_2, 0) };
    let mut replica_2 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_2, key_1, 0) };
    for message in test_messages() {
        let payload = Payload { message: message.plaintext.to_vec(), nonce: None, aad: None };
        let mut encrypted_payload = replica_1.encrypt(payload).unwrap();
        encrypted_payload.nonce = None; // Remove nonce to simulate missing nonce scenario
        let failed_decrypt = replica_2.decrypt(encrypted_payload);
        assert_that!(
            failed_decrypt,
            err(result_of!(|e: &anyhow::Error| e.to_string().contains("missing nonce"), eq(true)))
        );
    }
}

#[test]
fn test_unordered_encryptor_window_size_0() {
    let key_1 = &[42u8; SYMMETRIC_KEY_LEN];
    let key_2 = &[52u8; SYMMETRIC_KEY_LEN];
    let mut replica_1 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_1, key_2, 0) };
    let mut replica_2 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_2, key_1, 0) };
    let test_messages = test_messages();

    let encrypted_payload_1 = replica_1
        .encrypt(Payload { message: test_messages[0].plaintext.to_vec(), nonce: None, aad: None })
        .unwrap();
    let encrypted_payload_2 = replica_1
        .encrypt(Payload { message: test_messages[1].plaintext.to_vec(), nonce: None, aad: None })
        .unwrap();

    // Decrypt in reverse order
    let plaintext_2 = replica_2.decrypt(encrypted_payload_2).unwrap().message;
    assert_that!(test_messages[1].plaintext, eq(&plaintext_2));
    // Decrypting first message fails since it is from a lower nonce.
    assert_that!(replica_2.decrypt(encrypted_payload_1).is_err(), eq(true));
}

fn clone_payload(payload: &Payload) -> Payload {
    Payload {
        message: payload.message.clone(),
        nonce: payload.nonce.clone(),
        aad: payload.aad.clone(),
    }
}

#[test]
fn test_unordered_encryptor_window_size_3() {
    let key_1 = &[42u8; SYMMETRIC_KEY_LEN];
    let key_2 = &[52u8; SYMMETRIC_KEY_LEN];
    let test_messages = &[
        vec![1u8, 2u8, 3u8, 4u8],
        vec![4u8, 3u8, 2u8, 1u8],
        vec![1u8, 1u8, 1u8, 1u8],
        vec![2u8, 2u8, 2u8, 2u8],
        vec![3u8, 3u8, 3u8, 3u8],
        vec![4u8, 4u8, 4u8, 4u8],
    ];
    let mut replica_1 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_1, key_2, 3) };
    let mut replica_2 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_2, key_1, 3) };
    let mut encrypted_payloads = vec![];
    for item in test_messages {
        encrypted_payloads.push(
            replica_1.encrypt(Payload { message: item.to_vec(), nonce: None, aad: None }).unwrap(),
        );
    }

    // Out-of-order decryption
    let plaintext_3 = replica_2.decrypt(clone_payload(&encrypted_payloads[3])).unwrap();
    assert_that!(test_messages[3], eq(&plaintext_3.message));
    // Decrypting messages within the window should be ok.
    let plaintext_1 = replica_2.decrypt(clone_payload(&encrypted_payloads[1])).unwrap();
    assert_that!(test_messages[1], eq(&plaintext_1.message));
    let plaintext_2 = replica_2.decrypt(clone_payload(&encrypted_payloads[2])).unwrap();
    assert_that!(test_messages[2], eq(&plaintext_2.message));
    // Replaying message should fail.
    assert_that!(replica_2.decrypt(clone_payload(&encrypted_payloads[3])).is_err(), eq(true));
    assert_that!(replica_2.decrypt(clone_payload(&encrypted_payloads[2])).is_err(), eq(true));
    assert_that!(replica_2.decrypt(clone_payload(&encrypted_payloads[1])).is_err(), eq(true));
    // Decrypting messages outside the window should fail.
    assert_that!(replica_2.decrypt(clone_payload(&encrypted_payloads[0])).is_err(), eq(true));

    // Decrypt more messages in order.
    let plaintext_4 = replica_2.decrypt(clone_payload(&encrypted_payloads[4])).unwrap();
    assert_that!(test_messages[4], eq(&plaintext_4.message));
    let plaintext_5 = replica_2.decrypt(clone_payload(&encrypted_payloads[5])).unwrap();
    assert_that!(test_messages[5], eq(&plaintext_5.message));
}
