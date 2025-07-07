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

extern crate alloc;

use alloc::{
    boxed::Box,
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
};

use googletest::prelude::*;
use mockall::{mock, predicate as mockp};
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, AttestationResults, Endorsements, Evidence},
    session::v1::{Assertion, AttestRequest, AttestResponse, EndorsedEvidence, SessionBinding},
};

use crate::{
    attestation::{
        AttestationHandler, AttestationPublisher, ClientAttestationHandler, PeerAttestationVerdict,
        ServerAttestationHandler, VerifierResult,
    },
    config::AttestationHandlerConfig,
    generator::{AssertionGenerationError, AssertionGenerator, BindableAssertion},
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

mock! {
    TestAttestationPublisher {}
    impl AttestationPublisher for TestAttestationPublisher {
        fn publish(&
            self,
            endorsed_evidence: BTreeMap<String, EndorsedEvidence>,
            assertions: BTreeMap<String, Assertion>
        );
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

fn create_mock_attestation_publisher(
    expected_endorsed_evidence: BTreeMap<String, EndorsedEvidence>,
    expected_assertions: BTreeMap<String, Assertion>,
) -> Option<Arc<dyn AttestationPublisher>> {
    let mut publisher = MockTestAttestationPublisher::new();
    publisher
        .expect_publish()
        .with(mockp::eq(expected_endorsed_evidence), mockp::eq(expected_assertions))
        .return_const(())
        .times(1);
    Some(Arc::new(publisher))
}

fn create_mock_assertion_generator(assertion: Assertion) -> Arc<dyn AssertionGenerator> {
    let mut generator = MockTestAssertionGenerator::new();
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

    Ok(AttestationExchangeResults {
        client: client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        server: server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
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
    let client_config = AttestationHandlerConfig {
        attestation_publisher: create_mock_attestation_publisher(
            BTreeMap::default(),
            BTreeMap::default(),
        ),
        ..Default::default()
    };

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
    let server_config = AttestationHandlerConfig {
        attestation_publisher: create_mock_attestation_publisher(
            BTreeMap::default(),
            BTreeMap::default(),
        ),
        ..Default::default()
    };

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
        attestation_publisher: create_mock_attestation_publisher(
            BTreeMap::default(),
            BTreeMap::default(),
        ),
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
        attestation_publisher: create_mock_attestation_publisher(
            BTreeMap::default(),
            BTreeMap::default(),
        ),
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
            assertions: eq(&BTreeMap::from([(
                MATCHED_ATTESTER_ID1.to_string(),
                assertion.clone()
            )])),
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
            assertions: eq(&BTreeMap::from([(MATCHED_ATTESTER_ID1.to_string(), assertion)])),
            ..
        })))
    );

    Ok(())
}

#[googletest::test]
fn peer_attested_client_provides_request_accepts_response() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
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
        ..Default::default()
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
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
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
            create_passing_mock_verifier(),
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
        ..Default::default()
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
            create_passing_mock_verifier(),
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
fn client_failed_verifier_attestation_fails() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_failing_mock_verifier(),
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
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Verification failed"),
            attestation_results: elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(VerifierResult::Failure {
                    evidence: anything(),
                    result: anything()
                }),
            )),
        }),
        "Attestation should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn server_failed_verifier_attestation_fails() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_failing_mock_verifier(),
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
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Verification failed"),
            attestation_results: elements_are!((
                eq(MATCHED_ATTESTER_ID1),
                matches_pattern!(VerifierResult::Failure {
                    evidence: anything(),
                    result: anything()
                }),
            )),
        }),
        "Attestation should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn client_aggregated_attestation_succeeds() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
            (MATCHED_ATTESTER_ID2.to_string(), create_passing_mock_verifier()),
        ]),
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
        ..Default::default()
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed {
            attestation_results: unordered_elements_are!(
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
        }),
        "Attestation should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn server_aggregated_attestation_succeeds() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
            (MATCHED_ATTESTER_ID2.to_string(), create_passing_mock_verifier()),
        ]),
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
        ..Default::default()
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed {
            attestation_results: unordered_elements_are!(
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
        }),
        "Attestation should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn client_one_failed_verifier_aggregated_attestation_fails() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
            (MATCHED_ATTESTER_ID2.to_string(), create_failing_mock_verifier()),
            (UNMATCHED_VERIFIER_ID.to_string(), create_failing_mock_verifier()),
        ]),
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
        ..Default::default()
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Verification failed"),
            attestation_results: unordered_elements_are!(
                (
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(VerifierResult::Success {
                        evidence: anything(),
                        result: anything()
                    }),
                ),
                (
                    eq(MATCHED_ATTESTER_ID2),
                    matches_pattern!(VerifierResult::Failure {
                        evidence: anything(),
                        result: anything()
                    }),
                ),
                (eq(UNMATCHED_VERIFIER_ID), matches_pattern!(VerifierResult::Missing),),
                (
                    eq(UNMATCHED_ATTESTER_ID),
                    matches_pattern!(VerifierResult::Unverified { evidence: anything() }),
                )
            ),
        }),
        "Attestation should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn server_one_failed_verifier_aggregated_attestation_fails() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
            (MATCHED_ATTESTER_ID2.to_string(), create_failing_mock_verifier()),
            (UNMATCHED_VERIFIER_ID.to_string(), create_failing_mock_verifier()),
        ]),
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
        ..Default::default()
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    assert_that!(
        server_attestation_provider.take_attestation_state()?.peer_attestation_verdict,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: starts_with("Verification failed"),
            attestation_results: unordered_elements_are!(
                (
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(VerifierResult::Success {
                        evidence: anything(),
                        result: anything()
                    }),
                ),
                (
                    eq(MATCHED_ATTESTER_ID2),
                    matches_pattern!(VerifierResult::Failure {
                        evidence: anything(),
                        result: anything()
                    }),
                ),
                (eq(UNMATCHED_VERIFIER_ID), matches_pattern!(VerifierResult::Missing),),
                (
                    eq(UNMATCHED_ATTESTER_ID),
                    matches_pattern!(VerifierResult::Unverified { evidence: anything() }),
                )
            ),
        }),
        "Attestation type should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn client_unmatched_verifier_attestation_fails() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            UNMATCHED_VERIFIER_ID.to_string(),
            create_passing_mock_verifier(),
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
            reason: "No matching evidence is provided",
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
            create_passing_mock_verifier(),
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
            reason: "No matching evidence is provided",
            ..
        }),
        "Attestation should fail with an unmatched verifier"
    );

    Ok(())
}

#[googletest::test]
fn client_additional_attestation_passes() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
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
        ..Default::default()
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
    let server_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
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
        ..Default::default()
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
            create_passing_mock_verifier(),
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
            create_passing_mock_verifier(),
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

    // A second request should be ignored if the previous result has not been taken.
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
            create_passing_mock_verifier(),
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

        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
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
fn pairwise_bidirectional_attestation_fails() -> anyhow::Result<()> {
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
            create_failing_mock_verifier(),
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

        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_failing_mock_verifier(),
        )]),
        ..Default::default()
    };

    let results = do_attestation_exchange(client_config, server_config)?;

    assert_that!(
        results.client,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed { .. })
    );
    assert_that!(
        results.server,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed { .. })
    );

    Ok(())
}

#[googletest::test]
fn pairwise_compatible_attestation_types_verification_succeeds() -> anyhow::Result<()> {
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
            create_passing_mock_verifier(),
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
fn pairwise_incompatible_attestation_types_verification_fails() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
        ..Default::default()
    };
    let server_config = AttestationHandlerConfig {
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_endorser(),
        )]),

        peer_verifiers: BTreeMap::from([(
            UNMATCHED_VERIFIER_ID.to_string(),
            create_passing_mock_verifier(),
        )]),
        ..Default::default()
    };

    let results = do_attestation_exchange(client_config, server_config)?;

    assert_that!(
        results.client,
        matches_pattern!(PeerAttestationVerdict::AttestationPassed { .. })
    );
    assert_that!(
        results.server,
        matches_pattern!(PeerAttestationVerdict::AttestationFailed {
            reason: "No matching evidence is provided",
            ..
        })
    );

    Ok(())
}
