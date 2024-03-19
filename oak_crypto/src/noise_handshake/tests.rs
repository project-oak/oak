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
use alloc::vec;

use crate::noise_handshake::{respond, test_client::HandshakeInitiator, P256Scalar};

#[test]
fn process_handshake() {
    let test_messages = vec![vec![1u8, 2u8, 3u8, 4u8], vec![4u8, 3u8, 2u8, 1u8], vec![]];
    let identity_priv = P256Scalar::generate();
    let identity_pub_bytes = identity_priv.compute_public_key();
    let mut initiator = HandshakeInitiator::new(&identity_pub_bytes);
    let message = initiator.build_initial_message();
    let handshake_response = respond(identity_priv.bytes().as_slice(), &message).unwrap();
    let mut enclave_crypter = handshake_response.crypter;

    let (client_hash, mut client_crypter) =
        initiator.process_response(&handshake_response.response);
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
