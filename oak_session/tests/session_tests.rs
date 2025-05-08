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

extern crate alloc;

use googletest::prelude::*;
use mockall::mock;
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_crypto::verifier::Verifier;
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, AttestationResults, Endorsements, Evidence},
    session::v1::{
        session_request::Request, session_response::Response, PlaintextMessage, SessionRequest,
        SessionResponse,
    },
};
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType,
    key_extractor::KeyExtractor, session_binding::SessionBinder, ClientSession, ProtocolEngine,
    ServerSession, Session,
};

// Since [`Attester`], [`Endorser`] and [`AttestationVerifier`] are external
// traits, we have to use `mock!` instead of `[automock]` and define a test
// struct that implements those traits.
// <https://docs.rs/mockall/latest/mockall/#external-traits>
mock! {
    TestAttester {}
    impl Attester for TestAttester {
        fn extend(&mut self, encoded_event: &[u8]) -> anyhow::Result<()>;
        fn quote(&self) -> anyhow::Result<Evidence>;
    }
}

mock! {
    TestEndorser {}
    impl Endorser for TestEndorser {
        fn endorse<'a>(&self, evidence: Option<&'a Evidence>) -> anyhow::Result<Endorsements>;
    }
}

mock! {
    TestSessionBinder {}
    impl SessionBinder for TestSessionBinder {
        fn bind(&self, bound_data: &[u8]) -> Vec<u8>;
    }
}

mock! {
    TestAttestationVerifier {}
    impl AttestationVerifier for TestAttestationVerifier {
        fn verify(
            &self,
            evidence: &Evidence,
            endorsements: &Endorsements,
        ) -> anyhow::Result<AttestationResults>;
    }
}

mock! {
  TestKeyExtractor {}
  impl KeyExtractor for TestKeyExtractor {
    fn extract_verifying_key(
        &self,
        results: &AttestationResults,
    ) -> anyhow::Result<Box<dyn Verifier>>;
}
}

mock! {
   TestVerifier {}
   impl Verifier for TestVerifier {
       fn verify(&self, message: &[u8], signature: &[u8]) -> anyhow::Result<()>;
   }
}

fn create_mock_attester() -> Box<dyn Attester> {
    let mut attester = MockTestAttester::new();
    attester.expect_quote().returning(|| Ok(Evidence { ..Default::default() }));
    Box::new(attester)
}

fn create_mock_endorser() -> Box<dyn Endorser> {
    let mut endorser = MockTestEndorser::new();
    endorser.expect_endorse().returning(|_| Ok(Endorsements { ..Default::default() }));
    Box::new(endorser)
}

fn create_passing_mock_verifier() -> Box<dyn AttestationVerifier> {
    let mut verifier = MockTestAttestationVerifier::new();
    verifier.expect_verify().returning(move |_, _| {
        Ok(AttestationResults {
            status: attestation_results::Status::Success.into(),
            ..Default::default()
        })
    });
    Box::new(verifier)
}

fn create_mock_binder() -> Box<dyn SessionBinder> {
    let mut binder = MockTestSessionBinder::new();
    binder.expect_bind().returning(|_| vec![]);
    Box::new(binder)
}

fn create_mock_key_extractor() -> Box<dyn KeyExtractor> {
    let mut key_extractor = MockTestKeyExtractor::new();
    key_extractor.expect_extract_verifying_key().returning(|_| {
        let mut verifier = MockTestVerifier::new();
        verifier.expect_verify().returning(|_, _| Ok(()));
        Ok(Box::new(verifier))
    });
    Box::new(key_extractor)
}

const MATCHED_ATTESTER_ID1: &str = "MATCHED_ATTESTER_ID1";
const MATCHED_ATTESTER_ID2: &str = "MATCHED_ATTESTER_ID2";

#[googletest::test]
fn pairwise_nn_unattested_succeeds() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    let request = client_session
        .get_outgoing_message()
        .expect("An error occurred while getting the client outgoing message")
        .expect("No client outgoing message was produced");
    assert_that!(
        request,
        matches_pattern!(SessionRequest {
            request: some(matches_pattern!(Request::HandshakeRequest(anything())))
        }),
        "The first message sent by the client is a handshake request"
    );
    assert_that!(server_session.put_incoming_message(request), ok(some(())));

    let response = server_session
        .get_outgoing_message()
        .expect("An error occurred while getting the server outgoing message")
        .expect("No server outgoing message was produced");
    assert_that!(
        response,
        matches_pattern!(SessionResponse {
            response: some(matches_pattern!(Response::HandshakeResponse(anything())))
        }),
        "The first message sent by the server is a handshake response"
    );
    assert_that!(client_session.put_incoming_message(response), ok(some(())));

    assert_that!(client_session.is_open(), eq(true));
    assert_that!(server_session.is_open(), eq(true));

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nn_peer_self_succeeds() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

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

    assert_that!(client_session.is_open(), eq(true));
    assert_that!(server_session.is_open(), eq(true));

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nn_self_peer_broken() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

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

    let handshake_followup = client_session
        .get_outgoing_message()
        .expect("An error occurred while getting the client followup message")
        .expect("No client followup message was produced");
    assert_that!(
        client_session.is_open(),
        eq(true),
        "Getting the client followup message should make the session open"
    );

    assert_that!(
        handshake_followup,
        matches_pattern!(SessionRequest {
            request: some(matches_pattern!(Request::HandshakeRequest(anything())))
        }),
        "The message sent by the client is a handshake request"
    );
    assert_that!(server_session.put_incoming_message(handshake_followup), ok(some(())));
    assert_that!(server_session.get_outgoing_message(), ok(none()));

    assert_that!(client_session.is_open(), eq(true));
    assert_that!(server_session.is_open(), eq(true));

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nn_self_bidi() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID2.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID2.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID2.to_string(), create_mock_binder())
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

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

    let handshake_followup = client_session
        .get_outgoing_message()
        .expect("An error occurred while getting the client followup message")
        .expect("No client followup message was produced");
    assert_that!(
        client_session.is_open(),
        eq(true),
        "Getting the client followup message should make the session open"
    );

    assert_that!(
        handshake_followup,
        matches_pattern!(SessionRequest {
            request: some(matches_pattern!(Request::HandshakeRequest(anything())))
        }),
        "The message sent by the client is a handshake request"
    );
    assert_that!(server_session.put_incoming_message(handshake_followup), ok(some(())));
    assert_that!(server_session.get_outgoing_message(), ok(none()));

    assert_that!(client_session.is_open(), eq(true));
    assert_that!(server_session.is_open(), eq(true));

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nn_bidirectional_succeeds() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID2.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID2.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID2.to_string(), create_mock_binder())
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

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

    assert_that!(client_session.is_open(), eq(true));
    assert_that!(server_session.is_open(), eq(true));

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

fn invoke_hello_world(client_session: &mut ClientSession, server_session: &mut ServerSession) {
    assert_that!(client_session.write(PlaintextMessage { plaintext: "Hello".into() }), ok(()));
    let encrypted_request = client_session
        .get_outgoing_message()
        .expect("An error occurred while getting the client outgoing message")
        .expect("No client outgoing message was produced");
    assert_that!(
        encrypted_request,
        matches_pattern!(SessionRequest {
            request: some(matches_pattern!(Request::EncryptedMessage(anything())))
        }),
        "The client sent an encrypted message"
    );

    assert_that!(server_session.put_incoming_message(encrypted_request), ok(some(())));
    let decrypted_request = server_session
        .read()
        .expect("An error occurred while reading the decrypted incoming message")
        .expect("No decrypted incoming message was produced");
    assert_that!(decrypted_request.plaintext, eq("Hello".as_bytes()));

    assert_that!(server_session.write(PlaintextMessage { plaintext: "World".into() }), ok(()));
    let encrypted_response = server_session
        .get_outgoing_message()
        .expect("An error occurred while getting the server outgoing message")
        .expect("No server outgoing message was produced");
    assert_that!(
        encrypted_response,
        matches_pattern!(SessionResponse {
            response: some(matches_pattern!(Response::EncryptedMessage(anything())))
        }),
        "The server sent an encrypted message"
    );

    assert_that!(client_session.put_incoming_message(encrypted_response), ok(some(())));
    let decrypted_response = client_session
        .read()
        .expect("An error occurred while reading the decrypted incoming message")
        .expect("No decrypted incoming message was produced");
    assert_that!(decrypted_response.plaintext, eq("World".as_bytes()));
}
