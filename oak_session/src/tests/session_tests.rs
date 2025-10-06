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

use core::cell::RefCell;
use std::{
    boxed::Box,
    string::{String, ToString},
    sync::{Arc, Mutex},
    vec::Vec,
};

use anyhow::Context;
use googletest::prelude::*;
use mockall::mock;
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_crypto::{
    identity_key::{IdentityKey, IdentityKeyHandle},
    verifier::Verifier,
};
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, Assertion, AttestationResults, Endorsements, Evidence},
    session::v1::{
        session_request::Request, session_response::Response, EndorsedEvidence, PlaintextMessage,
        SessionBinding, SessionRequest, SessionResponse,
    },
};
use oak_session::{
    aggregators::PassThrough,
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    generator::{AssertionGenerationError, AssertionGenerator, BindableAssertion},
    handshake::HandshakeType,
    key_extractor::KeyExtractor,
    session::{AttestationEvidence, AttestationPublisher},
    session_binding::{SessionBinder, SessionBindingVerifier, SessionBindingVerifierProvider},
    verifier::{AssertionVerificationError, AssertionVerifier, VerifiedAssertion},
    ClientSession, ProtocolEngine, ServerSession, Session,
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

mock! {
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

struct TestAttestationPublisher {
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

impl AttestationPublisher for TestAttestationPublisher {
    fn publish(&self, attestation_evidence: AttestationEvidence) {
        *self.last_published.lock().expect("failed to lock publish item").borrow_mut() =
            Some(attestation_evidence)
    }
}

mock! {
    TestAssertionVerifier {}
    impl AssertionVerifier for TestAssertionVerifier {
        fn verify_assertion(
            &self,
            assertion: &Assertion,
        ) -> core::result::Result<Box<dyn VerifiedAssertion>, AssertionVerificationError>;
    }
}

mock! {
    #[derive(Debug)]
    TestVerifiedAssertion {}
    impl VerifiedAssertion for TestVerifiedAssertion {
        fn assertion(&self) -> &Assertion;
        fn verify_binding(
            &self,
            bound_data: &[u8],
            binding: &SessionBinding,
        ) -> core::result::Result<(), AssertionVerificationError>;
    }
}

mock! {
    TestAssertionGenerator {}
    impl AssertionGenerator for TestAssertionGenerator {
        fn generate(&self) -> core::result::Result<Box<dyn BindableAssertion>, AssertionGenerationError>;
    }
}

mock! {
    TestBindableAssertion {}
    impl BindableAssertion for TestBindableAssertion {
        fn assertion(&self) -> &Assertion;
        fn bind(&self, bound_data: &[u8]) -> core::result::Result<SessionBinding, AssertionGenerationError>;
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
    binder.expect_bind().returning(|bound_data| bound_data.to_vec());
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

fn create_mock_session_binding_verifier() -> Box<dyn SessionBindingVerifier> {
    let mut session_binding_verifier = MockTestSessionBindingVerifier::new();
    session_binding_verifier.expect_verify_binding().returning(|_, _| Ok(()));
    Box::new(session_binding_verifier)
}

fn create_mock_session_binding_verifier_provider() -> Box<dyn SessionBindingVerifierProvider> {
    let mut session_binding_verifier_provider = MockTestSessionBindingVerifierProvider::new();
    session_binding_verifier_provider
        .expect_create_session_binding_verifier()
        .returning(|_| Ok(create_mock_session_binding_verifier()));
    Box::new(session_binding_verifier_provider)
}

fn create_mock_assertion_generator(assertion: Assertion) -> Box<dyn AssertionGenerator> {
    let mut generator = MockTestAssertionGenerator::new();
    generator.expect_generate().returning(move || {
        let mut bindable_assertion = Box::new(MockTestBindableAssertion::new());
        bindable_assertion.expect_assertion().return_const(assertion.clone());
        bindable_assertion
            .expect_bind()
            .returning(|_| Ok(SessionBinding { binding: "test assertion binding".into() }));
        Ok(bindable_assertion)
    });
    Box::new(generator)
}

fn create_passing_mock_assertion_verifier(assertion: Assertion) -> Box<dyn AssertionVerifier> {
    let mut verifier = MockTestAssertionVerifier::new();
    verifier.expect_verify_assertion().returning(move |_| {
        let mut verified_assertion = Box::new(MockTestVerifiedAssertion::new());
        verified_assertion.expect_assertion().return_const(assertion.clone());
        verified_assertion.expect_verify_binding().returning(|_, _| Ok(()));
        Ok(verified_assertion)
    });
    Box::new(verifier)
}

#[derive(Debug, PartialEq)]
pub(super) enum HandshakeFollowup {
    Expected,
    NotExpected,
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

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nk_unattested_succeeds() -> anyhow::Result<()> {
    let identity_key = Box::new(IdentityKey::generate());
    let client_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_peer_static_public_key(identity_key.get_public_key().unwrap().as_slice())
        .build();
    let server_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_self_static_private_key(identity_key)
        .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[should_panic]
#[googletest::test]
fn pairwise_nk_unattested_mismatched_keys_fails() -> anyhow::Result<()> {
    let identity_key = Box::new(IdentityKey::generate());
    let wrong_identity_key = Box::new(IdentityKey::generate());
    let client_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_peer_static_public_key(identity_key.get_public_key().unwrap().as_slice())
        .build();
    let server_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_self_static_private_key(wrong_identity_key)
        .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    Ok(())
}

#[googletest::test]
fn pairwise_nn_unattested_self_succeeds() -> anyhow::Result<()> {
    let client_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let client_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN)
        .add_attestation_publisher(
            &(client_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
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

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    assert_that!(
        client_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: elements_are![(
                &MATCHED_ATTESTER_ID1.to_string(),
                &EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )],
            evidence_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID1.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            assertions: is_empty(),
            assertion_bindings: is_empty(),
            handshake_hash: not(is_empty()),
        }))
    );

    Ok(())
}

#[googletest::test]
fn pairwise_nn_self_unattested_compatible() -> anyhow::Result<()> {
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let client_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;
    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nn_peer_self_succeeds() -> anyhow::Result<()> {
    let client_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .add_peer_assertion_verifier(
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_assertion_verifier(assertion.clone()),
            )
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .add_attestation_publisher(
                &(client_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_self_assertion_generator(
                MATCHED_ATTESTER_ID2.to_string(),
                create_mock_assertion_generator(assertion.clone()),
            )
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    assert_that!(
        client_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: elements_are![(
                &MATCHED_ATTESTER_ID1.to_string(),
                &EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )],
            evidence_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID1.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            assertions: elements_are![(&MATCHED_ATTESTER_ID2.to_string(), &assertion)],
            assertion_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID2.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            handshake_hash: not(is_empty()),
        }))
    );

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

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected)?;
    assert_that!(server_session.get_outgoing_message(), ok(none()));

    assert_that!(client_session.is_open(), eq(true));
    assert_that!(server_session.is_open(), eq(true));

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nn_self_bidi() -> anyhow::Result<()> {
    let client_attestation_publisher = Arc::new(TestAttestationPublisher::new());
    let server_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let client_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .add_attestation_publisher(
                &(client_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
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
            .add_attestation_publisher(
                &(server_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    assert_that!(
        client_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: elements_are![(
                &MATCHED_ATTESTER_ID2.to_string(),
                &EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )],
            evidence_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID2.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            assertions: is_empty(),
            assertion_bindings: is_empty(),
            handshake_hash: not(is_empty()),
        }))
    );

    assert_that!(
        server_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: elements_are![(
                &MATCHED_ATTESTER_ID1.to_string(),
                &EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )],
            evidence_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID1.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            assertions: is_empty(),
            assertion_bindings: is_empty(),
            handshake_hash: not(is_empty()),
        }))
    );
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

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nn_peer_self_succeeds_custom_session_binding_verifier() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_binding_verifier_provider(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_session_binding_verifier_provider(),
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

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn get_peer_attestation_evidence() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_binding_verifier_provider(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_session_binding_verifier_provider(),
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

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    assert_that!(
        client_session.get_peer_attestation_evidence(),
        ok(matches_pattern!(AttestationEvidence {
            evidence: elements_are![(
                &MATCHED_ATTESTER_ID1.to_string(),
                &EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )],
            evidence_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID1.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            assertions: is_empty(),
            assertion_bindings: is_empty(),
            handshake_hash: not(is_empty()),
        }))
    );
    // The client does not send any attestation evidence/bindings to the server.
    assert_that!(
        server_session.get_peer_attestation_evidence(),
        ok(matches_pattern!(AttestationEvidence {
            evidence: is_empty(),
            evidence_bindings: is_empty(),
            assertions: is_empty(),
            assertion_bindings: is_empty(),
            handshake_hash: not(is_empty())
        }))
    );

    Ok(())
}

#[googletest::test]
fn test_session_sendable() -> anyhow::Result<()> {
    fn foo<T: Send>(_: T) {}

    fn test(s: ServerSession) {
        foo(s)
    }

    let identity_key = Box::new(IdentityKey::generate());
    let server_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_self_static_private_key(identity_key)
        .build();
    let server_session = ServerSession::create(server_config).unwrap();
    test(server_session);
    Ok(())
}

pub(super) fn do_attest(
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

pub(super) fn do_handshake(
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

/// SessionChannel/SessionInitializer Tests
#[googletest::gtest]
#[tokio::test]
async fn channel_unattested_nn_pair() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    channel_pair_test(client_config, server_config).await
}

#[googletest::gtest]
#[tokio::test]
async fn channel_nn_peer_self_succeeds() -> anyhow::Result<()> {
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
    channel_pair_test(client_config, server_config).await
}

#[googletest::gtest]
#[tokio::test]
async fn channel_bidi_nn_pair() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_binding_verifier_provider(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_session_binding_verifier_provider(),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();
    channel_pair_test(client_config, server_config).await
}

async fn channel_pair_test(
    client_config: SessionConfig,
    server_config: SessionConfig,
) -> anyhow::Result<()> {
    // Use channels for simple client-server implementation.
    let (client_tx, mut client_rx) = tokio::sync::mpsc::channel::<SessionRequest>(10);
    let (server_tx, mut server_rx) = tokio::sync::mpsc::channel::<SessionResponse>(10);

    // Start a server
    let server_join: tokio::task::JoinHandle<anyhow::Result<()>> = tokio::task::spawn(async move {
        let mut server_session = ServerSession::create(server_config)?;

        // Handshake Sequence
        while !server_session.is_open() {
            let next_request = client_rx.recv().await.context("getting next client message")?;
            server_session.handle_init_message(next_request).context("handling init message")?;
            if !server_session.is_open() {
                let next_response =
                    server_session.next_init_message().context("getting next init message")?;
                server_tx.send(next_response).await.context("sending response to client")?
            }
        }

        // Receive a Request
        let request: SessionRequest = client_rx.recv().await.context("receiving client request")?;
        let decrypted_request = server_session.decrypt(request).context("decrypting request")?;

        // Process Request
        let response = format!("Hello {}", String::from_utf8_lossy(decrypted_request.as_slice()));

        // Send Response
        let encrypted_response =
            server_session.encrypt(response.as_bytes()).context("encrypting response")?;
        server_tx.send(encrypted_response).await.context("sending response")?;

        // All done
        Ok(())
    });

    let mut client_session = ClientSession::create(client_config)?;

    // Handshake sequence
    while !client_session.is_open() {
        let request = client_session.next_init_message().expect("failed to get init messge");
        client_tx.send(request).await.expect("failed to send init message");
        let response = server_rx.recv().await.context("getting next server message")?;
        client_session.handle_init_message(response).expect("failed to handle init response");
    }

    // Send Message
    let message_to_server = client_session.encrypt(b"Mister Tester")?;
    client_tx.send(message_to_server).await.context("sending message to server")?;

    // Receive Response
    let response = server_rx.recv().await.context("getting server response")?;
    assert_that!(client_session.decrypt(response)?, eq(b"Hello Mister Tester"));

    server_join.await.context("joining server")?.context("server failing")
}
