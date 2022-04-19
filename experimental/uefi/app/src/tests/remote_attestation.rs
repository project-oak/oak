//
// Copyright 2022 The Project Oak Authors
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

//! Integration Test of Remote Attestation in UEFI.
//!
//! This tests that remote attestion works inside the UEFI app. While the test
//! code is identical to (a subset of) the tests in the remote attestation crate
//! they here utilize the qemu runner configured in the UEFI app. This means
//! that test code actually compiled to a UEFI target, which changes the
//! underlying implementation of the remote attestation crate.
//! TODO(#2654): It would be preferable to remove the test here, and instead
//! run the tests in the oak_remote_attestation crate itself for both standard
//! and UEFI targets. Due to concerns related to the workspace this is presently
//! not possible. Ref: https://github.com/project-oak/oak/issues/2654

extern crate alloc;

use alloc::{boxed::Box, sync::Arc};
use oak_remote_attestation::handshaker::{AttestationBehavior, ClientHandshaker, ServerHandshaker};

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
    let server_handshaker =
        ServerHandshaker::new(bidirectional_attestation, Arc::new(additional_info));

    (client_handshaker, server_handshaker)
}

#[test_case]
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
    assert_eq!(result, None);
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
