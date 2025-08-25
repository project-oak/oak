// Copyright 2025 The Project Oak Authors
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

use std::{sync::Arc, vec::Vec};

use googletest::prelude::*;
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::session::v1::{
    session_request::Request, session_response::Response, PlaintextMessage, SessionRequest,
    SessionResponse,
};
use oak_session::{
    attestation::AttestationType,
    config::SessionConfig,
    handshake::HandshakeType,
    session::{AttestationEvidence, Session},
    session_binding::{SessionBinder, SessionBindingVerifierProvider},
    ClientSession, ProtocolEngine, ServerSession,
};

#[derive(Debug, PartialEq)]
pub enum HandshakeFollowup {
    Expected,
    NotExpected,
}

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
pub fn test_unattested_nn_encryption_and_decryption_inner(message: Vec<u8>) {
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

pub fn test_verifier_success(
    attester: &Arc<dyn Attester>,
    endorser: &Arc<dyn Endorser>,
    session_binder: &Arc<dyn SessionBinder>,
    verifier: &Arc<dyn AttestationVerifier>,
    binding_verifier_provider: &Arc<dyn SessionBindingVerifierProvider>,
) {
    let attestation_id = "test_id".to_string();

    // We can use verification success both in the client and in the server session
    // simultaneously.
    let client_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester_ref(attestation_id.clone(), attester)
            .add_self_endorser_ref(attestation_id.clone(), endorser)
            .add_session_binder_ref(attestation_id.clone(), session_binder)
            .add_peer_verifier_with_binding_verifier_provider_ref(
                attestation_id.clone(),
                verifier,
                binding_verifier_provider,
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester_ref(attestation_id.clone(), attester)
            .add_self_endorser_ref(attestation_id.clone(), endorser)
            .add_session_binder_ref(attestation_id.clone(), session_binder)
            .add_peer_verifier_with_binding_verifier_provider_ref(
                attestation_id.clone(),
                verifier,
                binding_verifier_provider,
            )
            .build();

    let mut client_session = ClientSession::create(client_config).unwrap();
    let mut server_session = ServerSession::create(server_config).unwrap();

    do_attest(&mut client_session, &mut server_session).unwrap();
    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected).unwrap();
}

pub fn do_attest(
    client_session: &mut ClientSession,
    server_session: &mut ServerSession,
) -> anyhow::Result<()> {
    let attest_request = client_session
        .get_outgoing_message()
        .expect("An error occurred while getting the client outgoing message")
        .expect("No client outgoing message was produced");
    assert_that!(
        attest_request,
        matches_pattern!(SessionRequest {
            request: some(matches_pattern!(Request::AttestRequest(anything())))
        }),
        "The first message sent by the client is an attestation request"
    );
    assert_that!(server_session.put_incoming_message(attest_request), ok(some(())));

    let attest_response = server_session
        .get_outgoing_message()
        .expect("An error occurred while getting the server outgoing message")
        .expect("No server outgoing message was produced");
    assert_that!(
        attest_response,
        matches_pattern!(SessionResponse {
            response: some(matches_pattern!(Response::AttestResponse(anything())))
        }),
        "The first message sent by the server is an attestation response"
    );
    assert_that!(client_session.put_incoming_message(attest_response), ok(some(())));
    Ok(())
}

pub fn do_handshake(
    client_session: &mut ClientSession,
    server_session: &mut ServerSession,
    handshake_followup: HandshakeFollowup,
) -> anyhow::Result<()> {
    let handshake_request = client_session
        .get_outgoing_message()
        .expect("An error occurred while getting the client outgoing message")
        .expect("No client outgoing message was produced");
    assert_that!(
        handshake_request,
        matches_pattern!(SessionRequest {
            request: some(matches_pattern!(Request::HandshakeRequest(anything())))
        }),
        "The message sent by the client is a handshake request"
    );
    assert_that!(server_session.put_incoming_message(handshake_request), ok(some(())));
    let handshake_response = server_session
        .get_outgoing_message()
        .expect("An error occurred while getting the server outgoing message")
        .expect("No server outgoing message was produced");
    assert_that!(
        handshake_response,
        matches_pattern!(SessionResponse {
            response: some(matches_pattern!(Response::HandshakeResponse(anything())))
        }),
        "The message sent by the server is a handshake response"
    );
    assert_that!(client_session.put_incoming_message(handshake_response), ok(some(())));

    if handshake_followup == HandshakeFollowup::Expected {
        let handshake_followup = client_session
            .get_outgoing_message()
            .expect("An error occurred while getting the client followup message")
            .expect("No client followup message was produced");
        assert_that!(
            handshake_followup,
            matches_pattern!(SessionRequest {
                request: some(matches_pattern!(Request::HandshakeRequest(anything())))
            }),
            "The message sent by the client is a handshake request"
        );
        assert_that!(server_session.put_incoming_message(handshake_followup), ok(some(())));
        assert_that!(server_session.get_outgoing_message(), ok(none()));
    }

    assert_that!(client_session.is_open(), eq(true));
    assert_that!(server_session.is_open(), eq(true));
    assert_that!(
        server_session.get_session_binding_token(b"info").unwrap().as_slice(),
        eq(client_session.get_session_binding_token(b"info").unwrap().as_slice())
    );
    assert_that!(
        server_session.get_session_binding_token(b"info").unwrap().as_slice(),
        not(eq(client_session.get_session_binding_token(b"wrong info").unwrap().as_slice()))
    );
    assert_that!(
        client_session.get_peer_attestation_evidence()?,
        matches_pattern!(AttestationEvidence { evidence: anything(), .. })
    );
    Ok(())
}
