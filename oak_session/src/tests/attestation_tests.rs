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

extern crate std;

use std::{
    boxed::Box,
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
};

use googletest::prelude::*;
use mockall::mock;
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, Assertion, AttestationResults, Endorsements, Evidence},
    session::v1::{AttestRequest, AttestResponse, EndorsedEvidence, SessionBinding},
};
use oak_session::{
    aggregators::{All, PassThrough},
    attestation::{
        AttestationHandler, ClientAttestationHandler, PeerAttestationVerdict,
        ServerAttestationHandler, VerifierResult,
    },
    config::{AttestationHandlerConfig, PeerAttestationVerifier},
    generator::{BindableAssertion, BindableAssertionGenerator, BindableAssertionGeneratorError},
    session_binding::{SessionBindingVerifier, SessionBindingVerifierProvider},
    verifier::{
        BoundAssertionVerificationError, BoundAssertionVerifier, BoundAssertionVerifierResult,
        VerifiedBoundAssertion,
    },
    ProtocolEngine,
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
    TestBoundAssertionVerifier {}
    impl BoundAssertionVerifier for TestBoundAssertionVerifier {
        fn verify_assertion(
            &self,
            assertion: &Assertion,
        ) -> core::result::Result<Box<dyn VerifiedBoundAssertion>, BoundAssertionVerificationError>;
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

fn create_mock_attester() -> Arc<dyn Attester> {
    let mut attester = MockTestAttester::new();
    attester.expect_quote().returning(|| Ok(Evidence { ..Default::default() }));
    Arc::new(attester)
}

fn create_mock_endorser() -> Arc<dyn Endorser> {
    let mut endorser = MockTestEndorser::new();
    endorser.expect_endorse().returning(|_| Ok(Endorsements { ..Default::default() }));
    Arc::new(endorser)
}

fn create_passing_mock_verifier() -> Arc<dyn AttestationVerifier> {
    let mut verifier = MockTestAttestationVerifier::new();
    verifier.expect_verify().returning(|_, _| {
        Ok(AttestationResults {
            status: attestation_results::Status::Success.into(),
            ..Default::default()
        })
    });
    Arc::new(verifier)
}

fn create_failing_mock_verifier() -> Arc<dyn AttestationVerifier> {
    let mut verifier = MockTestAttestationVerifier::new();
    verifier.expect_verify().returning(|_, _| {
        Ok(AttestationResults {
            status: attestation_results::Status::GenericFailure.into(),
            reason: String::from("Mock failure"),
            ..Default::default()
        })
    });
    Arc::new(verifier)
}

fn create_passing_mock_assertion_verifier(assertion: Assertion) -> Arc<dyn BoundAssertionVerifier> {
    let mut verifier = MockTestBoundAssertionVerifier::new();
    verifier.expect_verify_assertion().returning(move |_| {
        let mut verified_bound_assertion = Box::new(MockTestVerifiedBoundAssertion::new());
        verified_bound_assertion.expect_assertion().return_const(assertion.clone());
        Ok(verified_bound_assertion)
    });
    Arc::new(verifier)
}

fn create_failing_mock_assertion_verifier() -> Arc<dyn BoundAssertionVerifier> {
    let mut verifier = MockTestBoundAssertionVerifier::new();
    verifier.expect_verify_assertion().returning(|_| {
        Err(BoundAssertionVerificationError::GenericFailure {
            error_msg: "Mock failure".to_string(),
        })
    });
    Arc::new(verifier)
}

fn create_mock_session_binding_verifier_provider() -> Arc<dyn SessionBindingVerifierProvider> {
    let mut session_binding_verifier_provider = MockTestSessionBindingVerifierProvider::new();
    session_binding_verifier_provider
        .expect_create_session_binding_verifier()
        .returning(|_| Ok(Box::new(MockTestSessionBindingVerifier::new())));
    Arc::new(session_binding_verifier_provider)
}

fn create_mock_assertion_generator(assertion: Assertion) -> Arc<dyn BindableAssertionGenerator> {
    let mut generator = MockTestBindableAssertionGenerator::new();
    generator.expect_generate().returning(move || {
        let mut bindable_assertion = Box::new(MockTestBindableAssertion::new());
        bindable_assertion.expect_assertion().return_const(assertion.clone());
        Ok(bindable_assertion)
    });
    Arc::new(generator)
}

struct AttestationExchangeResults {
    client: PeerAttestationVerdict,
    server: PeerAttestationVerdict,
}

fn do_attestation_exchange(
    client_config: AttestationHandlerConfig,
    server_config: AttestationHandlerConfig,
) -> anyhow::Result<AttestationExchangeResults> {
    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;
    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = client_attestation_provider
        .get_outgoing_message()
        .expect("Calling get_outgoing_message should return OK")
        .expect("An outgoing attest request should be available");
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    let attest_response = server_attestation_provider
        .get_outgoing_message()
        .expect("Calling get_outgoing_message should return OK")
        .expect("An outgoing attest response should be available");
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));

    let client_attestation_state = client_attestation_provider.take_attestation_state()?;
    let server_attestation_state = server_attestation_provider.take_attestation_state()?;
    assert_that!(
        client_attestation_state.attestation_binding_token,
        eq(&server_attestation_state.attestation_binding_token)
    );

    Ok(AttestationExchangeResults {
        client: client_attestation_state.peer_attestation_verdict,
        server: server_attestation_state.peer_attestation_verdict,
    })
}

const MATCHED_ATTESTER_ID1: &str = "MATCHED_ATTESTER_ID1";
const MATCHED_ATTESTER_ID2: &str = "MATCHED_ATTESTER_ID2";
const UNMATCHED_ATTESTER_ID: &str = "UNMATCHED_ATTESTER_ID";
const UNMATCHED_VERIFIER_ID: &str = "UNMATCHED_VERIFIER_ID";

/// Tests that test either client or server side in isolation.

#[googletest::test]
fn unattested_client_attestation_provides_empty_request() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig::default();

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_request = client_attestation_provider.get_outgoing_message();
    assert_that!(
        attest_request,
        ok(some(matches_pattern!(AttestRequest {
            endorsed_evidence: is_empty(),
            assertions: is_empty(),
        })))
    );

    Ok(())
}

#[googletest::test]
fn unattested_client_attestation_accepts_response() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig { ..Default::default() };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let result = client_attestation_provider.put_incoming_message(AttestResponse {
        endorsed_evidence: BTreeMap::from([]),
        ..Default::default()
    });

    assert_that!(result, ok(some(())));

    Ok(())
}

#[googletest::test]
fn unattested_server_attestation_accepts_request() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig { ..Default::default() };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request =
        AttestRequest { endorsed_evidence: BTreeMap::from([]), ..Default::default() };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    Ok(())
}

#[googletest::test]
fn unattested_server_attestation_provides_response() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig::default();

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    assert_that!(
        server_attestation_provider.get_outgoing_message(),
        ok(some(matches_pattern!(AttestResponse {
            endorsed_evidence: is_empty(),
            assertions: is_empty(),
        })))
    );

    Ok(())
}

#[googletest::test]
fn self_attested_client_provides_request_accepts_response() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_endorser(),
        )]),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    assert_that!(
        client_attestation_provider.get_outgoing_message(),
        ok(some(eq(&AttestRequest {
            endorsed_evidence: BTreeMap::from([(
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )]),
            ..Default::default()
        })))
    );

    let attest_response = AttestResponse { ..Default::default() };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));

    Ok(())
}

#[googletest::test]
fn self_attested_server_accepts_request_provides_response() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_endorser(),
        )]),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request =
        AttestRequest { endorsed_evidence: BTreeMap::from([]), ..Default::default() };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    let attest_response = server_attestation_provider.get_outgoing_message();
    assert_that!(
        attest_response,
        ok(some(eq(&AttestResponse {
            endorsed_evidence: BTreeMap::from([(
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )]),
            ..Default::default()
        })))
    );

    Ok(())
}

#[googletest::test]
fn client_with_assertion_generator_provides_request_with_assertion() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };

    let client_config = AttestationHandlerConfig {
        self_assertion_generators: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_assertion_generator(assertion.clone()),
        )]),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    assert_that!(
        client_attestation_provider.get_outgoing_message(),
        ok(some(matches_pattern!(AttestRequest {
            assertions: eq(&BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion,)])),
            ..
        })))
    );

    Ok(())
}

#[googletest::test]
fn server_with_assertion_generator_provides_response_with_assertion() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };

    let server_config = AttestationHandlerConfig {
        self_assertion_generators: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_assertion_generator(assertion.clone()),
        )]),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest::default();
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    assert_that!(
        server_attestation_provider.get_outgoing_message(),
        ok(some(matches_pattern!(AttestResponse {
            assertions: eq(&BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion,)])),
            ..
        })))
    );

    Ok(())
}

#[googletest::test]
fn peer_attested_client_provides_request_accepts_response() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_assertion_verifier(assertion.clone()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    assert_that!(
        client_attestation_provider.get_outgoing_message(),
        ok(some(eq(&AttestRequest {
            endorsed_evidence: BTreeMap::from([]),
            ..Default::default()
        })))
    );

    let attest_response = AttestResponse {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
        assertions: BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion)]),
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. })
    );

    Ok(())
}

#[googletest::test]
fn peer_attested_server_accepts_request_provides_response() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_assertion_verifier(assertion.clone()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
        assertions: BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion)]),
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    let attest_response = server_attestation_provider.get_outgoing_message();
    assert_that!(
        attest_response,
        ok(some(eq(&AttestResponse {
            endorsed_evidence: BTreeMap::from([]),
            ..Default::default()
        })))
    );

    Ok(())
}

#[googletest::test]
fn bidirectional_client_provides_request_accepts_response() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config = AttestationHandlerConfig {
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_endorser(),
        )]),

        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_assertion_verifier(assertion.clone()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    assert_that!(
        client_attestation_provider.get_outgoing_message(),
        ok(some(eq(&AttestRequest {
            endorsed_evidence: BTreeMap::from([(
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            )]),
            ..Default::default()
        })))
    );

    let attest_response = AttestResponse {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
        assertions: BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion)]),
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));

    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. })
    );

    Ok(())
}

#[googletest::test]
fn bidirectional_server_accepts_request_provides_response() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };
    let server_config = AttestationHandlerConfig {
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_mock_endorser(),
        )]),

        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_assertion_verifier(assertion.clone()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
        assertions: BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion)]),
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    let attest_response = server_attestation_provider.get_outgoing_message();
    assert_that!(
        attest_response,
        ok(some(eq(&AttestResponse {
            endorsed_evidence: BTreeMap::from([(
                MATCHED_ATTESTER_ID2.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            )]),
            ..Default::default()
        })))
    );

    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. })
    );

    Ok(())
}

#[googletest::test]
fn client_with_empty_peer_verifiers_fails() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig::default();

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_response =
        AttestResponse { endorsed_evidence: BTreeMap::from([]), ..Default::default() };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));

    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. }),
        "Attestation type should pass with an empty peer verifier map"
    );

    Ok(())
}

#[googletest::test]
fn server_with_empty_peer_verifiers_succeeds() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig::default();

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request =
        AttestRequest { endorsed_evidence: BTreeMap::from([]), ..Default::default() };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. }),
        "Attestation should pass with an empty peer verifier map"
    );

    Ok(())
}

#[googletest::test]
fn client_failed_evidence_verification_fails() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_failing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_assertion_verifier(assertion.clone()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_response = AttestResponse {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
        assertions: BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion)]),
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Legacy verification failed"),
            legacy_verification_results: elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(VerifierResult::Failure {
                    evidence: anything(),
                    result: anything()
                }),
            )),
            assertion_verification_results: elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(BoundAssertionVerifierResult::Success { .. })
            )),
        }),
        "Attestation should fail due to evidence verification failure"
    );

    Ok(())
}

#[googletest::test]
fn client_failed_assertion_verification_fails() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_failing_mock_assertion_verifier(),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_response = AttestResponse {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
        assertions: BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion)]),
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Assertion verification failed"),
            legacy_verification_results: elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(VerifierResult::Success {
                    evidence: anything(),
                    result: anything()
                }),
            )),
            assertion_verification_results: elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(BoundAssertionVerifierResult::Failure { .. })
            )),
        }),
        "Attestation should fail due to assertion verification failure"
    );

    Ok(())
}

#[googletest::test]
fn server_failed_evidence_verification_fails() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_failing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_assertion_verifier(assertion.clone()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
        assertions: BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion)]),
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Legacy verification failed"),
            legacy_verification_results: elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(VerifierResult::Failure {
                    evidence: anything(),
                    result: anything()
                }),
            )),
            assertion_verification_results: elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(BoundAssertionVerifierResult::Success { .. })
            )),
        }),
        "Attestation should fail due to evidence verification failure"
    );

    Ok(())
}

#[googletest::test]
fn server_failed_assertion_verification_fails() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_failing_mock_assertion_verifier(),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
        assertions: BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion)]),
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Assertion verification failed"),
            legacy_verification_results: elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(VerifierResult::Success {
                    evidence: anything(),
                    result: anything()
                }),
            )),
            assertion_verification_results: elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(BoundAssertionVerifierResult::Failure { .. })
            )),
        }),
        "Attestation should fail due to assertion verification failure"
    );

    Ok(())
}

#[googletest::test]
fn client_aggregated_attestation_succeeds() -> anyhow::Result<()> {
    let assertion1: Assertion = Assertion { content: "test1".as_bytes().to_vec() };
    let assertion2: Assertion = Assertion { content: "test2".as_bytes().to_vec() };
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                PeerAttestationVerifier {
                    verifier: create_passing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                PeerAttestationVerifier {
                    verifier: create_passing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
        ]),
        peer_assertion_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_assertion_verifier(assertion1.clone()),
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_assertion_verifier(assertion2.clone()),
            ),
        ]),
        assertion_attestation_aggregator: Box::new(All {}),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_response = AttestResponse {
        endorsed_evidence: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                UNMATCHED_ATTESTER_ID.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
        ]),
        assertions: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), assertion1),
            (MATCHED_ATTESTER_ID2.to_string(), assertion2),
        ]),
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed {
            legacy_verification_results: unordered_elements_are!(
                (
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(VerifierResult::Success {
                        evidence: anything(),
                        result: anything()
                    }),
                ),
                (
                    eq(MATCHED_ATTESTER_ID2),
                    matches_pattern!(VerifierResult::Success {
                        evidence: anything(),
                        result: anything()
                    }),
                ),
                (
                    eq(UNMATCHED_ATTESTER_ID),
                    matches_pattern!(VerifierResult::Unverified { evidence: anything() })
                )
            ),
            assertion_verification_results: unordered_elements_are!(
                (
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(BoundAssertionVerifierResult::Success { .. })
                ),
                (
                    eq(MATCHED_ATTESTER_ID2),
                    matches_pattern!(BoundAssertionVerifierResult::Success { .. })
                )
            ),
        }),
        "Attestation should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn server_aggregated_attestation_succeeds() -> anyhow::Result<()> {
    let assertion1: Assertion = Assertion { content: "test1".as_bytes().to_vec() };
    let assertion2: Assertion = Assertion { content: "test2".as_bytes().to_vec() };
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                PeerAttestationVerifier {
                    verifier: create_passing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                PeerAttestationVerifier {
                    verifier: create_passing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
        ]),
        peer_assertion_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_assertion_verifier(assertion1.clone()),
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_assertion_verifier(assertion2.clone()),
            ),
        ]),
        assertion_attestation_aggregator: Box::new(All {}),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest {
        endorsed_evidence: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                UNMATCHED_ATTESTER_ID.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
        ]),
        assertions: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), assertion1),
            (MATCHED_ATTESTER_ID2.to_string(), assertion2),
        ]),
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed {
            legacy_verification_results: unordered_elements_are!(
                (
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(VerifierResult::Success {
                        evidence: anything(),
                        result: anything()
                    }),
                ),
                (
                    eq(MATCHED_ATTESTER_ID2),
                    matches_pattern!(VerifierResult::Success {
                        evidence: anything(),
                        result: anything()
                    }),
                ),
                (
                    eq(UNMATCHED_ATTESTER_ID),
                    matches_pattern!(VerifierResult::Unverified { evidence: anything() }),
                )
            ),
            assertion_verification_results: unordered_elements_are!(
                (
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(BoundAssertionVerifierResult::Success { .. })
                ),
                (
                    eq(MATCHED_ATTESTER_ID2),
                    matches_pattern!(BoundAssertionVerifierResult::Success { .. })
                )
            ),
        }),
        "Attestation should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn client_one_failed_evidence_verifier_aggregated_attestation_fails() -> anyhow::Result<()> {
    let assertion1: Assertion = Assertion { content: "test1".as_bytes().to_vec() };
    let assertion2: Assertion = Assertion { content: "test2".as_bytes().to_vec() };
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                PeerAttestationVerifier {
                    verifier: create_passing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                PeerAttestationVerifier {
                    verifier: create_failing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
            (
                UNMATCHED_VERIFIER_ID.to_string(),
                PeerAttestationVerifier {
                    verifier: create_failing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
        ]),
        peer_assertion_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_assertion_verifier(assertion1.clone()),
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_assertion_verifier(assertion2.clone()),
            ),
            (UNMATCHED_VERIFIER_ID.to_string(), create_failing_mock_assertion_verifier()),
        ]),
        assertion_attestation_aggregator: Box::new(All {}),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_response = AttestResponse {
        endorsed_evidence: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                UNMATCHED_ATTESTER_ID.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
        ]),
        assertions: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), assertion1),
            (MATCHED_ATTESTER_ID2.to_string(), assertion2),
        ]),
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Legacy verification failed"),
            legacy_verification_results: unordered_elements_are!(
                (eq(MATCHED_ATTESTER_ID1), matches_pattern!(VerifierResult::Success { .. }),),
                (eq(MATCHED_ATTESTER_ID2), matches_pattern!(VerifierResult::Failure { .. }),),
                (eq(UNMATCHED_VERIFIER_ID), matches_pattern!(VerifierResult::Missing),),
                (eq(UNMATCHED_ATTESTER_ID), matches_pattern!(VerifierResult::Unverified { .. }),)
            ),
            assertion_verification_results: unordered_elements_are!(
                (
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(BoundAssertionVerifierResult::Success { .. })
                ),
                (
                    eq(MATCHED_ATTESTER_ID2),
                    matches_pattern!(BoundAssertionVerifierResult::Success { .. })
                ),
                (
                    eq(UNMATCHED_VERIFIER_ID),
                    matches_pattern!(BoundAssertionVerifierResult::Missing)
                )
            ),
        }),
        "Attestation should fail due to evidence verification failure"
    );

    Ok(())
}

#[googletest::test]
fn client_one_failed_assertion_verifier_aggregated_attestation_fails() -> anyhow::Result<()> {
    let assertion1: Assertion = Assertion { content: "test1".as_bytes().to_vec() };
    let assertion2: Assertion = Assertion { content: "test2".as_bytes().to_vec() };
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                PeerAttestationVerifier {
                    verifier: create_passing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                PeerAttestationVerifier {
                    verifier: create_passing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
            (
                UNMATCHED_VERIFIER_ID.to_string(),
                PeerAttestationVerifier {
                    verifier: create_failing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
        ]),
        peer_assertion_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_assertion_verifier(assertion1.clone()),
            ),
            (MATCHED_ATTESTER_ID2.to_string(), create_failing_mock_assertion_verifier()),
            (UNMATCHED_VERIFIER_ID.to_string(), create_failing_mock_assertion_verifier()),
        ]),
        assertion_attestation_aggregator: Box::new(All {}),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_response = AttestResponse {
        endorsed_evidence: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                UNMATCHED_ATTESTER_ID.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
        ]),
        assertions: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), assertion1),
            (MATCHED_ATTESTER_ID2.to_string(), assertion2),
        ]),
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Assertion verification failed"),
            legacy_verification_results: unordered_elements_are!(
                (eq(MATCHED_ATTESTER_ID1), matches_pattern!(VerifierResult::Success { .. }),),
                (eq(MATCHED_ATTESTER_ID2), matches_pattern!(VerifierResult::Success { .. }),),
                (eq(UNMATCHED_VERIFIER_ID), matches_pattern!(VerifierResult::Missing),),
                (eq(UNMATCHED_ATTESTER_ID), matches_pattern!(VerifierResult::Unverified { .. }),)
            ),
            assertion_verification_results: unordered_elements_are!(
                (
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(BoundAssertionVerifierResult::Success { .. })
                ),
                (
                    eq(MATCHED_ATTESTER_ID2),
                    matches_pattern!(BoundAssertionVerifierResult::Failure { .. })
                ),
                (
                    eq(UNMATCHED_VERIFIER_ID),
                    matches_pattern!(BoundAssertionVerifierResult::Missing)
                )
            ),
        }),
        "Attestation should fail due to assertion verification failure"
    );

    Ok(())
}

#[googletest::test]
fn server_one_failed_evidence_verifier_aggregated_attestation_fails() -> anyhow::Result<()> {
    let assertion1: Assertion = Assertion { content: "test1".as_bytes().to_vec() };
    let assertion2: Assertion = Assertion { content: "test2".as_bytes().to_vec() };
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                PeerAttestationVerifier {
                    verifier: create_passing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                PeerAttestationVerifier {
                    verifier: create_failing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
            (
                UNMATCHED_VERIFIER_ID.to_string(),
                PeerAttestationVerifier {
                    verifier: create_failing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
        ]),
        peer_assertion_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_assertion_verifier(assertion1.clone()),
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_assertion_verifier(assertion2.clone()),
            ),
            (UNMATCHED_VERIFIER_ID.to_string(), create_failing_mock_assertion_verifier()),
        ]),
        assertion_attestation_aggregator: Box::new(All {}),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest {
        endorsed_evidence: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                UNMATCHED_ATTESTER_ID.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
        ]),
        assertions: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), assertion1),
            (MATCHED_ATTESTER_ID2.to_string(), assertion2),
        ]),
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Legacy verification failed"),
            legacy_verification_results: unordered_elements_are!(
                (eq(MATCHED_ATTESTER_ID1), matches_pattern!(VerifierResult::Success { .. }),),
                (eq(MATCHED_ATTESTER_ID2), matches_pattern!(VerifierResult::Failure { .. }),),
                (eq(UNMATCHED_VERIFIER_ID), matches_pattern!(VerifierResult::Missing),),
                (eq(UNMATCHED_ATTESTER_ID), matches_pattern!(VerifierResult::Unverified { .. }),)
            ),
            assertion_verification_results: unordered_elements_are!(
                (
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(BoundAssertionVerifierResult::Success { .. })
                ),
                (
                    eq(MATCHED_ATTESTER_ID2),
                    matches_pattern!(BoundAssertionVerifierResult::Success { .. })
                ),
                (
                    eq(UNMATCHED_VERIFIER_ID),
                    matches_pattern!(BoundAssertionVerifierResult::Missing)
                )
            ),
        }),
        "Attestation should fail due to evidence verification failure"
    );

    Ok(())
}

#[googletest::test]
fn server_one_failed_assertion_verifier_aggregated_attestation_fails() -> anyhow::Result<()> {
    let assertion1: Assertion = Assertion { content: "test1".as_bytes().to_vec() };
    let assertion2: Assertion = Assertion { content: "test2".as_bytes().to_vec() };
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                PeerAttestationVerifier {
                    verifier: create_passing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                PeerAttestationVerifier {
                    verifier: create_passing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
            (
                UNMATCHED_VERIFIER_ID.to_string(),
                PeerAttestationVerifier {
                    verifier: create_failing_mock_verifier(),
                    binding_verifier_provider: create_mock_session_binding_verifier_provider(),
                },
            ),
        ]),
        peer_assertion_verifiers: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_assertion_verifier(assertion1.clone()),
            ),
            (MATCHED_ATTESTER_ID2.to_string(), create_failing_mock_assertion_verifier()),
            (UNMATCHED_VERIFIER_ID.to_string(), create_failing_mock_assertion_verifier()),
        ]),
        assertion_attestation_aggregator: Box::new(All {}),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest {
        endorsed_evidence: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                MATCHED_ATTESTER_ID2.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                UNMATCHED_ATTESTER_ID.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
        ]),
        assertions: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), assertion1),
            (MATCHED_ATTESTER_ID2.to_string(), assertion2),
        ]),
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Assertion verification failed"),
            legacy_verification_results: unordered_elements_are!(
                (eq(MATCHED_ATTESTER_ID1), matches_pattern!(VerifierResult::Success { .. }),),
                (eq(MATCHED_ATTESTER_ID2), matches_pattern!(VerifierResult::Success { .. }),),
                (eq(UNMATCHED_VERIFIER_ID), matches_pattern!(VerifierResult::Missing),),
                (eq(UNMATCHED_ATTESTER_ID), matches_pattern!(VerifierResult::Unverified { .. }),)
            ),
            assertion_verification_results: unordered_elements_are!(
                (
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(BoundAssertionVerifierResult::Success { .. })
                ),
                (
                    eq(MATCHED_ATTESTER_ID2),
                    matches_pattern!(BoundAssertionVerifierResult::Failure { .. })
                ),
                (
                    eq(UNMATCHED_VERIFIER_ID),
                    matches_pattern!(BoundAssertionVerifierResult::Missing)
                )
            ),
        }),
        "Attestation should fail due to assertion verification failure"
    );

    Ok(())
}

#[googletest::test]
fn client_unmatched_verifier_attestation_fails() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            UNMATCHED_VERIFIER_ID.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_response =
        AttestResponse { endorsed_evidence: BTreeMap::from([]), ..Default::default() };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    // This failure should mention what evidence is missing instead.
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: "Legacy verification failed: no matched legacy verifier found",
            ..
        }),
        "Attestation should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn server_unmatched_verifier_attestation_fails() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            UNMATCHED_VERIFIER_ID.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request =
        AttestRequest { endorsed_evidence: BTreeMap::from([]), ..Default::default() };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    // This failure should mention what evidence is missing instead.
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: "Legacy verification failed: no matched legacy verifier found",
            ..
        }),
        "Attestation should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn client_unmatched_assertion_verifier_attestation_fails() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        peer_assertion_verifiers: BTreeMap::from([(
            UNMATCHED_VERIFIER_ID.to_string(),
            create_passing_mock_assertion_verifier(Assertion::default()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_response = AttestResponse { assertions: BTreeMap::from([]), ..Default::default() };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: "Assertion verification failed: no matched bound assertion verifier found",
            ..
        }),
        "Attestation should fail with an unmatched assertion verifier"
    );

    Ok(())
}

#[googletest::test]
fn server_unmatched_assertion_verifier_attestation_fails() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        peer_assertion_verifiers: BTreeMap::from([(
            UNMATCHED_VERIFIER_ID.to_string(),
            create_passing_mock_assertion_verifier(Assertion::default()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest { assertions: BTreeMap::from([]), ..Default::default() };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: "Assertion verification failed: no matched bound assertion verifier found",
            ..
        }),
        "Attestation should fail with an unmatched assertion verifier"
    );

    Ok(())
}

#[googletest::test]
fn client_additional_attestation_passes() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_assertion_verifier(assertion.clone()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_response = AttestResponse {
        endorsed_evidence: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                UNMATCHED_ATTESTER_ID.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
        ]),
        assertions: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), assertion),
            (UNMATCHED_ATTESTER_ID.to_string(), Assertion::default()),
        ]),
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. })
    );

    Ok(())
}

#[googletest::test]
fn server_additional_attestation_passes() -> anyhow::Result<()> {
    let assertion: Assertion = Assertion { content: "test".as_bytes().to_vec() };
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_assertion_verifier(assertion.clone()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest {
        endorsed_evidence: BTreeMap::from([
            (
                MATCHED_ATTESTER_ID1.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
            (
                UNMATCHED_ATTESTER_ID.to_string(),
                EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() }),
                },
            ),
        ]),
        assertions: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), assertion),
            (UNMATCHED_ATTESTER_ID.to_string(), Assertion::default()),
        ]),
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. })
    );

    Ok(())
}

#[googletest::test]
fn client_receives_additional_attestations() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        ..Default::default()
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_response = AttestResponse {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
        ..Default::default()
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));

    // A second response should be ignored if the previous result has not been
    // taken.
    let ignored_response =
        AttestResponse { endorsed_evidence: BTreeMap::from([]), ..Default::default() };
    assert_that!(client_attestation_provider.put_incoming_message(ignored_response), ok(none()));

    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. })
    );

    Ok(())
}

#[googletest::test]
fn server_receives_additional_attestations() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        ..Default::default()
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
        ..Default::default()
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    // A second request should be ignored if the previous result has not been
    // taken.
    let ignored_request =
        AttestRequest { endorsed_evidence: BTreeMap::from([]), ..Default::default() };
    assert_that!(server_attestation_provider.put_incoming_message(ignored_request), ok(none()));

    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. })
    );

    Ok(())
}

/// Pairwise tests that combine a client and a server attester.

#[googletest::test]
fn pairwise_bidirectional_attestation_succeeds() -> anyhow::Result<()> {
    let client_assertion: Assertion = Assertion { content: "client_test".as_bytes().to_vec() };
    let server_assertion: Assertion = Assertion { content: "server_test".as_bytes().to_vec() };
    let client_config = AttestationHandlerConfig {
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_endorser(),
        )]),
        self_assertion_generators: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_assertion_generator(client_assertion.clone()),
        )]),

        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_passing_mock_assertion_verifier(server_assertion.clone()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };
    let server_config = AttestationHandlerConfig {
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_mock_endorser(),
        )]),
        self_assertion_generators: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_mock_assertion_generator(server_assertion.clone()),
        )]),

        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_passing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_assertion_verifier(client_assertion.clone()),
        )]),
        assertion_attestation_aggregator: Box::new(PassThrough {}),
        ..Default::default()
    };

    let results = do_attestation_exchange(client_config, server_config)?;

    assert_that!(
        results.client,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. })
    );
    assert_that!(
        results.server,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. })
    );

    Ok(())
}

#[googletest::test]
fn pairwise_bidirectional_attestation_fails_on_evidence() -> anyhow::Result<()> {
    let client_assertion: Assertion = Assertion { content: "client_test".as_bytes().to_vec() };
    let server_assertion: Assertion = Assertion { content: "server_test".as_bytes().to_vec() };
    let client_config = AttestationHandlerConfig {
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_endorser(),
        )]),
        self_assertion_generators: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_assertion_generator(client_assertion.clone()),
        )]),

        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            PeerAttestationVerifier {
                verifier: create_failing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_passing_mock_assertion_verifier(server_assertion.clone()),
        )]),
        ..Default::default()
    };
    let server_config = AttestationHandlerConfig {
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_mock_endorser(),
        )]),
        self_assertion_generators: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_mock_assertion_generator(server_assertion.clone()),
        )]),

        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            PeerAttestationVerifier {
                verifier: create_failing_mock_verifier(),
                binding_verifier_provider: create_mock_session_binding_verifier_provider(),
            },
        )]),
        peer_assertion_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_assertion_verifier(client_assertion.clone()),
        )]),
        ..Default::default()
    };

    let results = do_attestation_exchange(client_config, server_config)?;

    assert_that!(
        results.client,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            legacy_verification_results: unordered_elements_are!((
                eq(MATCHED_ATTESTER_ID2),
                matches_pattern!(VerifierResult::Failure { .. })
            )),
            assertion_verification_results: unordered_elements_are!((
                eq(MATCHED_ATTESTER_ID2),
                matches_pattern!(BoundAssertionVerifierResult::Success { .. })
            )),
            ..
        })
    );
    assert_that!(
        results.server,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            legacy_verification_results: unordered_elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(VerifierResult::Failure { .. })
            )),
            assertion_verification_results: unordered_elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(BoundAssertionVerifierResult::Success { .. })
            )),
            ..
        })
    );

    Ok(())
}
