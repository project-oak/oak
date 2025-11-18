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

use std::{
    cell::RefCell,
    sync::{Arc, Mutex},
    vec::Vec,
};

use anyhow::{anyhow, Context};
use googletest::prelude::*;
use mockall::mock;
use oak_attestation_types::{
    assertion_generator::{AssertionGenerator, AssertionGeneratorError},
    attester::Attester,
    endorser::Endorser,
};
use oak_attestation_verification_types::{
    assertion_verifier::{AssertionVerifier, AssertionVerifierError},
    verifier::AttestationVerifier,
};
use oak_crypto::verifier::Verifier;
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results::Status, Assertion, AttestationResults, Endorsements, Evidence,
    },
    session::v1::{
        session_request::Request, session_response::Response, PlaintextMessage, SessionBinding,
        SessionRequest, SessionResponse,
    },
};
use oak_session::{
    attestation::AttestationType,
    config::SessionConfig,
    generator::{
        BindableAssertion, BindableAssertionGenerator, BindableAssertionGeneratorError,
        SessionKeyBindableAssertionGenerator,
    },
    handshake::HandshakeType,
    key_extractor::KeyExtractor,
    session::{AttestationEvidence, AttestationPublisher, Session},
    session_binding::{SessionBinder, SessionBindingVerifier, SessionBindingVerifierProvider},
    verifier::{
        BoundAssertionVerificationError, BoundAssertionVerifier, SessionKeyBoundAssertionVerifier,
        VerifiedBoundAssertion,
    },
    ClientSession, ProtocolEngine, ServerSession,
};
use oak_time::{clock::FixedClock, make_instant, Instant};
use p256::ecdsa::SigningKey;
use rand_core::OsRng;

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
        .context("An error occurred while getting the client outgoing message")?
        .context("No client outgoing message was produced")?;
    assert_that!(
        attest_request,
        matches_pattern!(SessionRequest {
            request: some(matches_pattern!(Request::AttestRequest(anything())))
        }),
        "The first message sent by the client is an attestation request"
    );
    server_session.put_incoming_message(attest_request)?;

    let attest_response = server_session
        .get_outgoing_message()
        .context("An error occurred while getting the server outgoing message")?
        .context("No server outgoing message was produced")?;
    assert_that!(
        attest_response,
        matches_pattern!(SessionResponse {
            response: some(matches_pattern!(Response::AttestResponse(anything())))
        }),
        "The first message sent by the server is an attestation response"
    );
    client_session.put_incoming_message(attest_response)?;
    Ok(())
}

pub fn do_handshake(
    client_session: &mut ClientSession,
    server_session: &mut ServerSession,
    handshake_followup: HandshakeFollowup,
) -> anyhow::Result<()> {
    let handshake_request = client_session
        .get_outgoing_message()
        .context("An error occurred while getting the client outgoing message")?
        .context("No client outgoing message was produced")?;
    assert_that!(
        handshake_request,
        matches_pattern!(SessionRequest {
            request: some(matches_pattern!(Request::HandshakeRequest(anything())))
        }),
        "The message sent by the client is a handshake request"
    );
    server_session.put_incoming_message(handshake_request)?;
    let handshake_response = server_session
        .get_outgoing_message()
        .context("An error occurred while getting the server outgoing message")?
        .context("No server outgoing message was produced")?;
    assert_that!(
        handshake_response,
        matches_pattern!(SessionResponse {
            response: some(matches_pattern!(Response::HandshakeResponse(anything())))
        }),
        "The message sent by the server is a handshake response"
    );
    assert_that!(client_session.put_incoming_message(handshake_response)?, some(()));

    if handshake_followup == HandshakeFollowup::Expected {
        let handshake_followup = client_session
            .get_outgoing_message()
            .context("An error occurred while getting the client followup message")?
            .context("No client followup message was produced")?;
        assert_that!(
            handshake_followup,
            matches_pattern!(SessionRequest {
                request: some(matches_pattern!(Request::HandshakeRequest(anything())))
            }),
            "The message sent by the client is a handshake request"
        );
        assert_that!(server_session.put_incoming_message(handshake_followup)?, some(()));
        assert_that!(server_session.get_outgoing_message()?, none());
    }

    assert_that!(client_session.is_open(), eq(true));
    assert_that!(server_session.is_open(), eq(true));
    assert_that!(
        server_session.get_session_binding_token(b"info")?.as_slice(),
        eq(client_session.get_session_binding_token(b"info")?.as_slice())
    );
    assert_that!(
        server_session.get_session_binding_token(b"info")?.as_slice(),
        not(eq(client_session.get_session_binding_token(b"wrong info")?.as_slice()))
    );
    assert_that!(
        client_session.get_peer_attestation_evidence()?,
        matches_pattern!(AttestationEvidence { evidence: anything(), .. })
    );
    Ok(())
}

pub fn invoke_hello_world(client_session: &mut ClientSession, server_session: &mut ServerSession) {
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

// Useful mocks

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
    #[derive(Debug)]
   TestVerifier {}
   impl Verifier for TestVerifier {
       fn verify(&self, message: &[u8], signature: &[u8]) -> anyhow::Result<()>;
   }
}

mock! {
    #[derive(Debug)]
    TestSessionBindingVerifier {}
    impl SessionBindingVerifier for TestSessionBindingVerifier {
        fn verify_binding(&self, bound_data: &[u8], binding: &[u8]) -> anyhow::Result<()>;
    }
}

mock! {
    TestSessionBindingVerifierProvider {}
    impl SessionBindingVerifierProvider for TestSessionBindingVerifierProvider {
        fn create_session_binding_verifier(
            &self,
            attestation_results: &AttestationResults,
        ) -> anyhow::Result<Box<dyn SessionBindingVerifier>>;
    }
}

pub struct TestAttestationPublisher {
    pub last_published: Mutex<RefCell<Option<AttestationEvidence>>>,
}

impl TestAttestationPublisher {
    pub fn new() -> Self {
        Self { last_published: Mutex::new(RefCell::new(None)) }
    }

    pub fn take(&self) -> Option<AttestationEvidence> {
        self.last_published.lock().expect("failed to lock publish item").borrow_mut().take()
    }
}

impl Default for TestAttestationPublisher {
    fn default() -> Self {
        Self::new()
    }
}

impl AttestationPublisher for TestAttestationPublisher {
    fn publish(&self, attestation_evidence: AttestationEvidence) {
        *self.last_published.lock().expect("failed to lock publish item").borrow_mut() =
            Some(attestation_evidence)
    }
}

mock! {
    TestAssertionVerifier {}
    impl AssertionVerifier for TestAssertionVerifier {
        fn verify(
            &self,
            assertion: &Assertion,
            asserted_data: &[u8],
            verification_time: Instant,
        ) -> core::result::Result<(), AssertionVerifierError>;
    }
}

mock! {
    TestAssertionGenerator {}
    impl AssertionGenerator for TestAssertionGenerator {
        fn generate(&self, asserted_data: &[u8]) -> core::result::Result<Assertion, AssertionGeneratorError>;
    }
}

mock! {
    TestBoundAssertionVerifier {}
    impl BoundAssertionVerifier for TestBoundAssertionVerifier {
        fn verify_assertion(
            &self,
            assertion: &Assertion,
        ) -> core::result::Result<Box<dyn VerifiedBoundAssertion>, BoundAssertionVerificationError>;
    }
}

mock! {
    TestBindableAssertionGenerator {}
    impl BindableAssertionGenerator for TestBindableAssertionGenerator {
        fn generate(&self) -> core::result::Result<Box<dyn BindableAssertion>, BindableAssertionGeneratorError>;
    }
}

mock! {
    TestBindableAssertion {}
    impl BindableAssertion for TestBindableAssertion {
        fn assertion(&self) -> &Assertion;
        fn bind(&self, bound_data: &[u8]) -> core::result::Result<SessionBinding, BindableAssertionGeneratorError>;
    }
}

mock! {
    #[derive(Debug)]
    TestVerifiedBoundAssertion {}
    impl VerifiedBoundAssertion for TestVerifiedBoundAssertion {
        fn assertion(&self) -> &Assertion;
        fn verify_binding(
            &self,
            bound_data: &[u8],
            binding: &SessionBinding,
        ) -> core::result::Result<(), BoundAssertionVerificationError>;
    }
}

pub fn create_mock_attester() -> Box<dyn Attester> {
    let mut attester = MockTestAttester::new();
    attester.expect_quote().returning(|| Ok(Evidence { ..Default::default() }));
    Box::new(attester)
}

pub fn create_mock_endorser() -> Box<dyn Endorser> {
    let mut endorser = MockTestEndorser::new();
    endorser.expect_endorse().returning(|_| Ok(Endorsements { ..Default::default() }));
    Box::new(endorser)
}

pub fn create_passing_mock_verifier() -> Box<dyn AttestationVerifier> {
    let mut verifier = MockTestAttestationVerifier::new();
    verifier.expect_verify().returning(move |_, _| {
        Ok(AttestationResults { status: Status::Success.into(), ..Default::default() })
    });
    Box::new(verifier)
}

pub fn create_failing_mock_verifier() -> Box<dyn AttestationVerifier> {
    let mut verifier = MockTestAttestationVerifier::new();
    verifier.expect_verify().returning(move |_, _| {
        Ok(AttestationResults {
            status: Status::GenericFailure.into(),
            reason: "mock attestation failure".to_string(),
            ..Default::default()
        })
    });
    Box::new(verifier)
}

pub fn create_mock_binder() -> Box<dyn SessionBinder> {
    let mut binder = MockTestSessionBinder::new();
    binder.expect_bind().returning(|bound_data| bound_data.to_vec());
    Box::new(binder)
}

pub fn create_mock_key_extractor() -> Box<dyn KeyExtractor> {
    let mut key_extractor = MockTestKeyExtractor::new();
    key_extractor.expect_extract_verifying_key().returning(|_| {
        let mut verifier = MockTestVerifier::new();
        verifier.expect_verify().returning(|_, _| Ok(()));
        Ok(Box::new(verifier))
    });
    Box::new(key_extractor)
}

pub fn create_mock_session_binding_verifier() -> Box<dyn SessionBindingVerifier> {
    let mut session_binding_verifier = MockTestSessionBindingVerifier::new();
    session_binding_verifier.expect_verify_binding().returning(|_, _| Ok(()));
    Box::new(session_binding_verifier)
}

pub fn create_mock_session_binding_verifier_provider() -> Box<dyn SessionBindingVerifierProvider> {
    let mut session_binding_verifier_provider = MockTestSessionBindingVerifierProvider::new();
    session_binding_verifier_provider
        .expect_create_session_binding_verifier()
        .returning(|_| Ok(create_mock_session_binding_verifier()));
    Box::new(session_binding_verifier_provider)
}

pub fn create_failing_mock_session_binding_verifier_provider(
) -> Box<dyn SessionBindingVerifierProvider> {
    let mut session_binding_verifier = MockTestSessionBindingVerifier::new();
    session_binding_verifier
        .expect_verify_binding()
        .returning(|_, _| Err(anyhow::anyhow!("mock session binding verification failure")));
    let mut session_binding_verifier_provider = MockTestSessionBindingVerifierProvider::new();
    session_binding_verifier_provider.expect_create_session_binding_verifier().returning(
        move |_| {
            let mut session_binding_verifier = MockTestSessionBindingVerifier::new();
            session_binding_verifier.expect_verify_binding().returning(|_, _| {
                Err(anyhow::anyhow!("mock session binding verification failure"))
            });
            Ok(Box::new(session_binding_verifier))
        },
    );
    Box::new(session_binding_verifier_provider)
}

pub fn create_mock_assertion_generator(
    assertion: Assertion,
) -> Box<dyn BindableAssertionGenerator> {
    let mut generator = MockTestBindableAssertionGenerator::new();
    generator.expect_generate().returning(move || {
        let mut bindable_assertion = Box::new(MockTestBindableAssertion::new());
        bindable_assertion.expect_assertion().return_const(assertion.clone());
        Ok(bindable_assertion)
    });
    Box::new(generator)
}

pub fn create_passing_mock_assertion_verifier(
    assertion: Assertion,
) -> Box<dyn BoundAssertionVerifier> {
    let mut verifier = MockTestBoundAssertionVerifier::new();
    verifier.expect_verify_assertion().returning(move |_| {
        let mut verified_bound_assertion = Box::new(MockTestVerifiedBoundAssertion::new());
        verified_bound_assertion.expect_assertion().return_const(assertion.clone());
        Ok(verified_bound_assertion)
    });
    Box::new(verifier)
}

pub fn create_failing_mock_assertion_verifier() -> Box<dyn BoundAssertionVerifier> {
    let mut verifier = MockTestBoundAssertionVerifier::new();
    verifier.expect_verify_assertion().returning(|_| {
        Err(BoundAssertionVerificationError::GenericFailure {
            error_msg: "Mock failure".to_string(),
        })
    });
    Box::new(verifier)
}

pub fn create_mock_session_key_assertion_generator(
    assertion: Assertion,
) -> Box<dyn BindableAssertionGenerator> {
    let mut generator = MockTestAssertionGenerator::new();
    generator.expect_generate().returning(move |_| Ok(assertion.clone()));
    Box::new(
        SessionKeyBindableAssertionGenerator::create_with_assertion_generator(
            &generator,
            Arc::new(SigningKey::random(&mut OsRng)),
        )
        .expect("assertion generator creation failed"),
    )
}

pub fn create_passing_mock_session_key_assertion_verifier() -> Box<dyn BoundAssertionVerifier> {
    let mut verifier = MockTestAssertionVerifier::new();
    verifier.expect_verify().returning(|_, _, _| Ok(()));
    Box::new(SessionKeyBoundAssertionVerifier {
        assertion_verifier: Arc::new(verifier),
        clock: Arc::new(FixedClock::at_instant(make_instant!("2025-10-14T17:31:32Z"))),
    })
}

pub fn create_failing_mock_session_key_assertion_verifier() -> Box<dyn BoundAssertionVerifier> {
    let mut verifier = MockTestAssertionVerifier::new();
    verifier
        .expect_verify()
        .returning(|_, _, _| Err(AssertionVerifierError::Other(anyhow!("Mock failure"))));
    Box::new(SessionKeyBoundAssertionVerifier {
        assertion_verifier: Arc::new(verifier),
        clock: Arc::new(FixedClock::at_instant(make_instant!("2025-10-14T17:31:32Z"))),
    })
}
