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
    crypto::Signer,
    handshaker::{
        create_attestation_info, verify_attestation_info, AttestationBehavior, ClientHandshaker,
        ServerHandshaker,
    },
    tests::message::INVALID_MESSAGE_HEADER,
};
use assert_matches::assert_matches;

const TEE_MEASUREMENT: &str = "Test TEE measurement";
const DATA: [u8; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

fn create_handshakers() -> (ClientHandshaker, ServerHandshaker) {
    let bidirectional_attestation =
        AttestationBehavior::create_bidirectional_attestation(&[], TEE_MEASUREMENT.as_bytes())
            .unwrap();
    let client_handshaker = ClientHandshaker::new(
        bidirectional_attestation,
        Box::new(|server_identity| {
            if !server_identity.additional_info.is_empty() {
                Ok(())
            } else {
                anyhow::bail!("No additional info provided.")
            }
        }),
    );

    let bidirectional_attestation =
        AttestationBehavior::create_bidirectional_attestation(&[], TEE_MEASUREMENT.as_bytes())
            .unwrap();

    let additional_info = br"Additional Info".to_vec();
    let server_handshaker = ServerHandshaker::new(bidirectional_attestation, additional_info);

    (client_handshaker, server_handshaker)
}

#[test]
fn test_create_attestation_behavior() {
    let self_attestation = AttestationBehavior::create_self_attestation(&[]);
    assert_matches!(self_attestation, Ok(_));

    let bidirectional_attestation = AttestationBehavior::create_bidirectional_attestation(&[], &[]);
    assert_matches!(bidirectional_attestation, Ok(_));
}

#[test]
fn test_handshake() {
    let (mut client_handshaker, mut server_handshaker) = create_handshakers();

    let client_hello = client_handshaker
        .create_client_hello()
        .expect("Couldn't create client hello message");

    let server_identity = server_handshaker
        .next_step(&client_hello)
        .expect("Couldn't process client hello message")
        .expect("Empty server identity message");

    let client_identity = client_handshaker
        .next_step(&server_identity)
        .expect("Couldn't process server identity message")
        .expect("Empty client identity message");
    assert!(client_handshaker.is_completed());

    let result = server_handshaker
        .next_step(&client_identity)
        .expect("Couldn't process client identity message");
    assert_matches!(result, None);
    assert!(server_handshaker.is_completed());

    let mut client_encryptor = client_handshaker
        .get_encryptor()
        .expect("Couldn't get client encryptor");
    let mut server_encryptor = server_handshaker
        .get_encryptor()
        .expect("Couldn't get server encryptor");

    let encrypted_client_data = client_encryptor
        .encrypt(&DATA)
        .expect("Couldn't encrypt client data");
    let decrypted_client_data = server_encryptor
        .decrypt(&encrypted_client_data)
        .expect("Couldn't decrypt client data");
    assert_eq!(decrypted_client_data, DATA);

    let encrypted_server_data = server_encryptor
        .encrypt(&DATA)
        .expect("Couldn't encrypt server data");
    let decrypted_server_data = client_encryptor
        .decrypt(&encrypted_server_data)
        .expect("Couldn't decrypt server data");
    assert_eq!(decrypted_server_data, DATA);
}

#[test]
fn test_invalid_message_after_initialization() {
    let (mut client_handshaker, mut server_handshaker) = create_handshakers();
    let invalid_message = vec![INVALID_MESSAGE_HEADER];

    let result = client_handshaker.next_step(&invalid_message);
    assert_matches!(result, Err(_));
    assert!(client_handshaker.is_aborted());
    let result = client_handshaker.create_client_hello();
    assert_matches!(result, Err(_));

    let result = server_handshaker.next_step(&invalid_message);
    assert_matches!(result, Err(_));
    assert!(server_handshaker.is_aborted());
}

#[test]
fn test_invalid_message_after_hello() {
    let (mut client_handshaker, mut server_handshaker) = create_handshakers();
    let invalid_message = vec![INVALID_MESSAGE_HEADER];

    let client_hello = client_handshaker.create_client_hello().unwrap();
    let result = client_handshaker.next_step(&invalid_message);
    assert_matches!(result, Err(_));
    assert!(client_handshaker.is_aborted());

    let server_identity = server_handshaker.next_step(&client_hello).unwrap().unwrap();
    let result = server_handshaker.next_step(&invalid_message);
    assert_matches!(result, Err(_));
    assert!(server_handshaker.is_aborted());

    let result = client_handshaker.next_step(&server_identity);
    assert_matches!(result, Err(_));
}

#[test]
fn test_invalid_message_after_identities() {
    let (mut client_handshaker, mut server_handshaker) = create_handshakers();
    let invalid_message = vec![INVALID_MESSAGE_HEADER];

    let client_hello = client_handshaker.create_client_hello().unwrap();
    let server_identity = server_handshaker.next_step(&client_hello).unwrap().unwrap();
    let client_identity = client_handshaker
        .next_step(&server_identity)
        .unwrap()
        .unwrap();

    let result = client_handshaker.next_step(&invalid_message);
    assert_matches!(result, Err(_));
    assert!(client_handshaker.is_aborted());

    let result = server_handshaker.next_step(&invalid_message);
    assert_matches!(result, Err(_));
    assert!(server_handshaker.is_aborted());

    let result = server_handshaker.next_step(&client_identity);
    assert_matches!(result, Err(_));
}

#[test]
fn test_replay_server_identity() {
    let (mut first_client_handshaker, mut first_server_handshaker) = create_handshakers();
    let (mut second_client_handshaker, _) = create_handshakers();

    let first_client_hello = first_client_handshaker.create_client_hello().unwrap();
    let first_server_identity = first_server_handshaker
        .next_step(&first_client_hello)
        .unwrap()
        .unwrap();

    let _ = second_client_handshaker.create_client_hello().unwrap();
    let result = second_client_handshaker.next_step(&first_server_identity);
    assert_matches!(result, Err(_));
    assert!(second_client_handshaker.is_aborted());
}

#[test]
fn test_replay_client_identity() {
    let (mut first_client_handshaker, mut first_server_handshaker) = create_handshakers();
    let (mut second_client_handshaker, mut second_server_handshaker) = create_handshakers();

    let first_client_hello = first_client_handshaker.create_client_hello().unwrap();
    let first_server_identity = first_server_handshaker
        .next_step(&first_client_hello)
        .unwrap()
        .unwrap();
    let first_client_identity = first_client_handshaker
        .next_step(&first_server_identity)
        .unwrap()
        .unwrap();

    let second_client_hello = second_client_handshaker.create_client_hello().unwrap();
    let _ = second_server_handshaker
        .next_step(&second_client_hello)
        .unwrap()
        .unwrap();
    let result = second_server_handshaker.next_step(&first_client_identity);
    assert_matches!(result, Err(_));
}

#[test]
fn test_attestation_info_roundtrip() {
    let signer = Signer::create().expect("could not create signer");
    let additional_info = br"Additional info";
    let tee_certificate = br"TEE certificate";
    let attestation_info = create_attestation_info(&signer, additional_info, tee_certificate)
        .expect("could not create attestation info.");

    let result = verify_attestation_info(attestation_info.as_ref(), TEE_MEASUREMENT.as_bytes());
    assert!(result.is_ok());
}
