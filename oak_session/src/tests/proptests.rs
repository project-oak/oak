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

use oak_proto_rust::oak::session::v1::PlaintextMessage;
use proptest::prelude::*;

use super::session_tests::{do_attest, do_handshake, HandshakeFollowup};
use crate::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType,
    session::Session, ClientSession, ProtocolEngine, ServerSession,
};

// Test that the Oak Session can encrypt and decrypt messages correctly in an
// unattested session. This test uses the `proptest` crate to generate random
// messages for testing, and makes sure that the messages can be encrypted by
// the client, sent to the server, decrypted by the server, and then sent back
// to the client, where it is decrypted again.
//
// This function is the inner implementation of the test, which is called by
// the `proptest!` macro. It is separated out to allow it to be reused as part
// of a future binary or test that will be tied to falsifiable claims expressed
// as Oak Transparent Release Endorsements.
fn test_unattested_nn_encryption_and_decryption_inner(message: Vec<u8>) {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();

    let mut client_session = ClientSession::create(client_config).unwrap();
    let mut server_session = ServerSession::create(server_config).unwrap();

    do_attest(&mut client_session, &mut server_session).unwrap();

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected).unwrap();

    // Test client to server communication.
    client_session.write(PlaintextMessage { plaintext: message.clone() }).unwrap();
    let encrypted_request = client_session.get_outgoing_message().unwrap().unwrap();
    server_session.put_incoming_message(encrypted_request).unwrap();
    let decrypted_request = server_session.read().unwrap().unwrap();
    assert_eq!(decrypted_request.plaintext, message);

    // Test server to client communication.
    server_session.write(PlaintextMessage { plaintext: message.clone() }).unwrap();
    let encrypted_response = server_session.get_outgoing_message().unwrap().unwrap();
    client_session.put_incoming_message(encrypted_response).unwrap();
    let decrypted_response = client_session.read().unwrap().unwrap();
    assert_eq!(decrypted_response.plaintext, message);
}

proptest! {
    #[test]
    fn test_unattested_nn_encryption_and_decryption(message: Vec<u8>) {
        test_unattested_nn_encryption_and_decryption_inner(message)
    }
}
