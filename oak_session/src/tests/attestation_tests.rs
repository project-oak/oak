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
use mockall::mock;
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, AttestationResults, Endorsements, Evidence},
    session::v1::{AttestRequest, AttestResponse, EndorsedEvidence},
};

use crate::{
    attestation::{
        AttestationHandler, AttestationType, AttestationVerdict, ClientAttestationHandler,
        DefaultVerifierResultsAggregator, ServerAttestationHandler, VerifierResult,
    },
    config::AttestationHandlerConfig,
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

struct AttestationExchangeResults {
    client: anyhow::Result<AttestationVerdict>,
    server: anyhow::Result<AttestationVerdict>,
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
        client: client_attestation_provider.take_attestation_verdict(),
        server: server_attestation_provider.take_attestation_verdict(),
    })
}

const MATCHED_ATTESTER_ID1: &str = "MATCHED_ATTESTER_ID1";
const MATCHED_ATTESTER_ID2: &str = "MATCHED_ATTESTER_ID2";
const UNMATCHED_ATTESTER_ID: &str = "UNMATCHED_ATTESTER_ID";
const UNMATCHED_VERIFIER_ID: &str = "UNMATCHED_VERIFIER_ID";

/// Tests that test either client or server side in isolation.

#[googletest::test]
fn unattested_client_attestation_provides_empty_request() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Unattested,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let attest_request = client_attestation_provider.get_outgoing_message();
    assert_that!(
        attest_request,
        ok(some(matches_pattern!(AttestRequest { endorsed_evidence: empty() })))
    );

    Ok(())
}

#[googletest::test]
fn unattested_client_attestation_accepts_response() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Unattested,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    let result = client_attestation_provider
        .put_incoming_message(AttestResponse { endorsed_evidence: BTreeMap::from([]) });

    assert_that!(result, ok(some(())));

    Ok(())
}

#[googletest::test]
fn unattested_server_attestation_accepts_request() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Unattested,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest { endorsed_evidence: BTreeMap::from([]) };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    Ok(())
}

#[googletest::test]
fn unattested_server_attestation_provides_response() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Unattested,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    assert_that!(
        server_attestation_provider.get_outgoing_message(),
        ok(some(matches_pattern!(AttestResponse { endorsed_evidence: empty() })))
    );

    Ok(())
}

#[googletest::test]
fn self_attested_client_provides_request_accepts_response() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::SelfUnidirectional,
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_endorser(),
        )]),
        peer_verifiers: BTreeMap::from([]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
            )])
        })))
    );

    let attest_response = AttestResponse { endorsed_evidence: BTreeMap::from([]) };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));

    Ok(())
}

#[googletest::test]
fn self_attested_server_accepts_request_provides_response() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::SelfUnidirectional,
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_endorser(),
        )]),
        peer_verifiers: BTreeMap::from([]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };

    let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

    let attest_request = AttestRequest { endorsed_evidence: BTreeMap::from([]) };
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
            )])
        })))
    );

    Ok(())
}

#[googletest::test]
fn peer_attested_client_provides_request_accepts_response() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::PeerUnidirectional,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };

    let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

    assert_that!(
        client_attestation_provider.get_outgoing_message(),
        ok(some(eq(&AttestRequest { endorsed_evidence: BTreeMap::from([]) })))
    );

    let attest_response = AttestResponse {
        endorsed_evidence: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            EndorsedEvidence {
                evidence: Some(Evidence { ..Default::default() }),
                endorsements: Some(Endorsements { ..Default::default() }),
            },
        )]),
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_verdict(),
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );

    Ok(())
}

#[googletest::test]
fn peer_attested_server_accepts_request_provides_response() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::PeerUnidirectional,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    let attest_response = server_attestation_provider.get_outgoing_message();
    assert_that!(
        attest_response,
        ok(some(eq(&AttestResponse { endorsed_evidence: BTreeMap::from([]) })))
    );

    Ok(())
}

#[googletest::test]
fn bidirectional_client_provides_request_accepts_response() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Bidirectional,
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
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
            )])
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
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));

    assert_that!(
        client_attestation_provider.take_attestation_verdict(),
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );

    Ok(())
}

#[googletest::test]
fn bidirectional_server_accepts_request_provides_response() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Bidirectional,
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
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
            )])
        })))
    );

    assert_that!(
        server_attestation_provider.take_attestation_verdict(),
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );

    Ok(())
}

#[googletest::test]
fn client_with_empty_peer_verifiers_fails() -> anyhow::Result<()> {
    for attestation_type in [AttestationType::PeerUnidirectional, AttestationType::Bidirectional] {
        let client_config = AttestationHandlerConfig {
            attestation_type,
            self_attesters: BTreeMap::from([]),
            self_endorsers: BTreeMap::from([]),
            peer_verifiers: BTreeMap::from([]),
            attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
        };

        let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

        let attest_response = AttestResponse { endorsed_evidence: BTreeMap::from([]) };
        assert_that!(
            client_attestation_provider.put_incoming_message(attest_response),
            ok(some(()))
        );

        assert_that!(
            client_attestation_provider.take_attestation_verdict(),
            ok(matches_pattern!(AttestationVerdict::AttestationFailed {
                reason: "No matching attestation results",
                ..
            })),
            "Attestation type {attestation_type:?} should fail with an empty peer verifier map"
        );
    }

    Ok(())
}

#[googletest::test]
fn server_with_empty_peer_verifiers_fails() -> anyhow::Result<()> {
    for attestation_type in [AttestationType::PeerUnidirectional, AttestationType::Bidirectional] {
        let server_config = AttestationHandlerConfig {
            attestation_type,
            self_attesters: BTreeMap::from([]),
            self_endorsers: BTreeMap::from([]),
            peer_verifiers: BTreeMap::from([]),
            attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
        };

        let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

        let attest_request = AttestRequest { endorsed_evidence: BTreeMap::from([]) };
        assert_that!(
            server_attestation_provider.put_incoming_message(attest_request),
            ok(some(()))
        );

        assert_that!(
            server_attestation_provider.take_attestation_verdict(),
            ok(matches_pattern!(AttestationVerdict::AttestationFailed {
                reason: "No matching attestation results",
                ..
            })),
            "Attestation type {attestation_type:?} should fail with an empty peer verifier map"
        );
    }

    Ok(())
}

#[googletest::test]
fn client_failed_verifier_attestation_fails() -> anyhow::Result<()> {
    for attestation_type in [AttestationType::PeerUnidirectional, AttestationType::Bidirectional] {
        let client_config = AttestationHandlerConfig {
            attestation_type,
            self_attesters: BTreeMap::from([]),
            self_endorsers: BTreeMap::from([]),
            peer_verifiers: BTreeMap::from([(
                MATCHED_ATTESTER_ID1.to_string(),
                create_failing_mock_verifier(),
            )]),
            attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
        };
        assert_that!(
            client_attestation_provider.put_incoming_message(attest_response),
            ok(some(()))
        );
        assert_that!(
            client_attestation_provider.take_attestation_verdict(),
            ok(matches_pattern!(AttestationVerdict::AttestationFailed {
                reason: starts_with("Verification failed"),
                attestation_results: elements_are!((
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(VerifierResult::Failure(anything())),
                )),
            })),
            "Attestation type {attestation_type:?} should fail with an unmatched verifier"
        );
    }

    Ok(())
}

#[googletest::test]
fn server_failed_verifier_attestation_fails() -> anyhow::Result<()> {
    for attestation_type in [AttestationType::PeerUnidirectional, AttestationType::Bidirectional] {
        let server_config = AttestationHandlerConfig {
            attestation_type,
            self_attesters: BTreeMap::from([]),
            self_endorsers: BTreeMap::from([]),
            peer_verifiers: BTreeMap::from([(
                MATCHED_ATTESTER_ID1.to_string(),
                create_failing_mock_verifier(),
            )]),
            attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
        };
        assert_that!(
            server_attestation_provider.put_incoming_message(attest_request),
            ok(some(()))
        );
        assert_that!(
            server_attestation_provider.take_attestation_verdict(),
            ok(matches_pattern!(AttestationVerdict::AttestationFailed {
                reason: starts_with("Verification failed"),
                attestation_results: elements_are!((
                    eq(MATCHED_ATTESTER_ID1),
                    matches_pattern!(VerifierResult::Failure(anything())),
                )),
            })),
            "Attestation type {attestation_type:?} should fail with an unmatched verifier"
        );
    }

    Ok(())
}

#[googletest::test]
fn client_aggregated_attestation_succeeds() -> anyhow::Result<()> {
    for attestation_type in [AttestationType::PeerUnidirectional, AttestationType::Bidirectional] {
        let client_config = AttestationHandlerConfig {
            attestation_type,
            self_attesters: BTreeMap::from([]),
            self_endorsers: BTreeMap::from([]),
            peer_verifiers: BTreeMap::from([
                (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
                (MATCHED_ATTESTER_ID2.to_string(), create_passing_mock_verifier()),
                // Failures in an unmatched verifier are irrelevant as it is never invoked
                (UNMATCHED_VERIFIER_ID.to_string(), create_failing_mock_verifier()),
            ]),
            attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
        };
        assert_that!(
            client_attestation_provider.put_incoming_message(attest_response),
            ok(some(()))
        );
        assert_that!(
            client_attestation_provider.take_attestation_verdict(),
            ok(matches_pattern!(AttestationVerdict::AttestationPassed {
                attestation_results: unordered_elements_are!(
                    (
                        eq(MATCHED_ATTESTER_ID1),
                        matches_pattern!(VerifierResult::Success(anything())),
                    ),
                    (
                        eq(MATCHED_ATTESTER_ID2),
                        matches_pattern!(VerifierResult::Success(anything())),
                    ),
                    (eq(UNMATCHED_VERIFIER_ID), matches_pattern!(VerifierResult::Missing),),
                    (
                        eq(UNMATCHED_ATTESTER_ID),
                        matches_pattern!(VerifierResult::Unverified(anything()))
                    )
                ),
            })),
            "Attestation type {attestation_type:?} should fail with an unmatched verifier"
        );
    }

    Ok(())
}

#[googletest::test]
fn server_aggregated_attestation_succeeds() -> anyhow::Result<()> {
    for attestation_type in [AttestationType::PeerUnidirectional, AttestationType::Bidirectional] {
        let server_config = AttestationHandlerConfig {
            attestation_type,
            self_attesters: BTreeMap::from([]),
            self_endorsers: BTreeMap::from([]),
            peer_verifiers: BTreeMap::from([
                (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
                (MATCHED_ATTESTER_ID2.to_string(), create_passing_mock_verifier()),
                // Failures in an unmatched verifier are irrelevant as it is never invoked
                (UNMATCHED_VERIFIER_ID.to_string(), create_failing_mock_verifier()),
            ]),
            attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
        };
        assert_that!(
            server_attestation_provider.put_incoming_message(attest_request),
            ok(some(()))
        );
        assert_that!(
            server_attestation_provider.take_attestation_verdict(),
            ok(matches_pattern!(AttestationVerdict::AttestationPassed {
                attestation_results: unordered_elements_are!(
                    (
                        eq(MATCHED_ATTESTER_ID1),
                        matches_pattern!(VerifierResult::Success(anything())),
                    ),
                    (
                        eq(MATCHED_ATTESTER_ID2),
                        matches_pattern!(VerifierResult::Success(anything())),
                    ),
                    (eq(UNMATCHED_VERIFIER_ID), matches_pattern!(VerifierResult::Missing),),
                    (
                        eq(UNMATCHED_ATTESTER_ID),
                        matches_pattern!(VerifierResult::Unverified(anything())),
                    )
                ),
            })),
            "Attestation type {attestation_type:?} should fail with an unmatched verifier"
        );
    }

    Ok(())
}

#[googletest::test]
fn client_one_failed_verifier_aggregated_attestation_fails() -> anyhow::Result<()> {
    for attestation_type in [AttestationType::PeerUnidirectional, AttestationType::Bidirectional] {
        let client_config = AttestationHandlerConfig {
            attestation_type,
            self_attesters: BTreeMap::from([]),
            self_endorsers: BTreeMap::from([]),
            peer_verifiers: BTreeMap::from([
                (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
                (MATCHED_ATTESTER_ID2.to_string(), create_failing_mock_verifier()),
                (UNMATCHED_VERIFIER_ID.to_string(), create_failing_mock_verifier()),
            ]),
            attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
        };
        assert_that!(
            client_attestation_provider.put_incoming_message(attest_response),
            ok(some(()))
        );
        assert_that!(
            client_attestation_provider.take_attestation_verdict(),
            ok(matches_pattern!(AttestationVerdict::AttestationFailed {
                reason: starts_with("Verification failed"),
                attestation_results: unordered_elements_are!(
                    (
                        eq(MATCHED_ATTESTER_ID1),
                        matches_pattern!(VerifierResult::Success(anything())),
                    ),
                    (
                        eq(MATCHED_ATTESTER_ID2),
                        matches_pattern!(VerifierResult::Failure(anything())),
                    ),
                    (eq(UNMATCHED_VERIFIER_ID), matches_pattern!(VerifierResult::Missing),),
                    (
                        eq(UNMATCHED_ATTESTER_ID),
                        matches_pattern!(VerifierResult::Unverified(anything())),
                    )
                ),
            })),
            "Attestation type {attestation_type:?} should fail with an unmatched verifier"
        );
    }

    Ok(())
}

#[googletest::test]
fn server_one_failed_verifier_aggregated_attestation_fails() -> anyhow::Result<()> {
    for attestation_type in [AttestationType::PeerUnidirectional, AttestationType::Bidirectional] {
        let server_config = AttestationHandlerConfig {
            attestation_type,
            self_attesters: BTreeMap::from([]),
            self_endorsers: BTreeMap::from([]),
            peer_verifiers: BTreeMap::from([
                (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
                (MATCHED_ATTESTER_ID2.to_string(), create_failing_mock_verifier()),
                (UNMATCHED_VERIFIER_ID.to_string(), create_failing_mock_verifier()),
            ]),
            attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
        };
        assert_that!(
            server_attestation_provider.put_incoming_message(attest_request),
            ok(some(()))
        );
        assert_that!(
            server_attestation_provider.take_attestation_verdict(),
            ok(matches_pattern!(AttestationVerdict::AttestationFailed {
                reason: starts_with("Verification failed"),
                attestation_results: unordered_elements_are!(
                    (
                        eq(MATCHED_ATTESTER_ID1),
                        matches_pattern!(VerifierResult::Success(anything())),
                    ),
                    (
                        eq(MATCHED_ATTESTER_ID2),
                        matches_pattern!(VerifierResult::Failure(anything())),
                    ),
                    (eq(UNMATCHED_VERIFIER_ID), matches_pattern!(VerifierResult::Missing),),
                    (
                        eq(UNMATCHED_ATTESTER_ID),
                        matches_pattern!(VerifierResult::Unverified(anything())),
                    )
                ),
            })),
            "Attestation type {attestation_type:?} should fail with an unmatched verifier"
        );
    }

    Ok(())
}

#[googletest::test]
fn client_unmatched_verifier_attestation_fails() -> anyhow::Result<()> {
    for attestation_type in [AttestationType::PeerUnidirectional, AttestationType::Bidirectional] {
        let client_config = AttestationHandlerConfig {
            attestation_type,
            self_attesters: BTreeMap::from([]),
            self_endorsers: BTreeMap::from([]),
            peer_verifiers: BTreeMap::from([(
                UNMATCHED_VERIFIER_ID.to_string(),
                create_passing_mock_verifier(),
            )]),
            attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
        };

        let mut client_attestation_provider = ClientAttestationHandler::create(client_config)?;

        let attest_response = AttestResponse { endorsed_evidence: BTreeMap::from([]) };
        assert_that!(
            client_attestation_provider.put_incoming_message(attest_response),
            ok(some(()))
        );
        // This failure should mention what evidence is missing instead.
        assert_that!(
            client_attestation_provider.take_attestation_verdict(),
            ok(matches_pattern!(AttestationVerdict::AttestationFailed {
                reason: "No matching attestation results",
                ..
            })),
            "Attestation type {attestation_type:?} should fail with an unmatched verifier"
        );
    }

    Ok(())
}

#[googletest::test]
fn server_unmatched_verifier_attestation_fails() -> anyhow::Result<()> {
    for attestation_type in [AttestationType::PeerUnidirectional, AttestationType::Bidirectional] {
        let server_config = AttestationHandlerConfig {
            attestation_type,
            self_attesters: BTreeMap::from([]),
            self_endorsers: BTreeMap::from([]),
            peer_verifiers: BTreeMap::from([(
                UNMATCHED_VERIFIER_ID.to_string(),
                create_passing_mock_verifier(),
            )]),
            attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
        };

        let mut server_attestation_provider = ServerAttestationHandler::create(server_config)?;

        let attest_request = AttestRequest { endorsed_evidence: BTreeMap::from([]) };
        assert_that!(
            server_attestation_provider.put_incoming_message(attest_request),
            ok(some(()))
        );
        // This failure should mention what evidence is missing instead.
        assert_that!(
            server_attestation_provider.take_attestation_verdict(),
            ok(matches_pattern!(AttestationVerdict::AttestationFailed {
                reason: "No matching attestation results",
                ..
            })),
            "Attestation type {attestation_type:?} should fail with an unmatched verifier"
        );
    }

    Ok(())
}

#[googletest::test]
fn client_additional_attestation_passes() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::PeerUnidirectional,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));
    assert_that!(
        client_attestation_provider.take_attestation_verdict(),
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );

    Ok(())
}

#[googletest::test]
fn server_additional_attestation_passes() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::PeerUnidirectional,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));
    assert_that!(
        server_attestation_provider.take_attestation_verdict(),
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );

    Ok(())
}

#[googletest::test]
fn client_receives_additional_attestations() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::PeerUnidirectional,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
    };
    assert_that!(client_attestation_provider.put_incoming_message(attest_response), ok(some(())));

    // A second response should be ignored if the previous result has not been
    // taken.
    let ignored_response = AttestResponse { endorsed_evidence: BTreeMap::from([]) };
    assert_that!(client_attestation_provider.put_incoming_message(ignored_response), ok(none()));

    assert_that!(
        client_attestation_provider.take_attestation_verdict(),
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );

    Ok(())
}

#[googletest::test]
fn server_receives_additional_attestations() -> anyhow::Result<()> {
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::PeerUnidirectional,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
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
    };
    assert_that!(server_attestation_provider.put_incoming_message(attest_request), ok(some(())));

    // A second request should be ignored if the previous result has not been taken.
    let ignored_request = AttestRequest { endorsed_evidence: BTreeMap::from([]) };
    assert_that!(server_attestation_provider.put_incoming_message(ignored_request), ok(none()));

    assert_that!(
        server_attestation_provider.take_attestation_verdict(),
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );

    Ok(())
}

/// Pairwise tests that combine a client and a server attester.

#[googletest::test]
fn pairwise_bidirectional_attestation_succeeds() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Bidirectional,
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
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Bidirectional,
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
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };

    let results = do_attestation_exchange(client_config, server_config)?;

    assert_that!(
        results.client,
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );
    assert_that!(
        results.server,
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );

    Ok(())
}

#[googletest::test]
fn pairwise_bidirectional_attestation_fails() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Bidirectional,
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
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Bidirectional,
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
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };

    let results = do_attestation_exchange(client_config, server_config)?;

    assert_that!(
        results.client,
        ok(matches_pattern!(AttestationVerdict::AttestationFailed { .. }))
    );
    assert_that!(
        results.server,
        ok(matches_pattern!(AttestationVerdict::AttestationFailed { .. }))
    );

    Ok(())
}

#[googletest::test]
fn pairwise_compatible_attestation_types_verification_succeeds() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Bidirectional,
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
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::SelfUnidirectional,
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID2.to_string(),
            create_mock_endorser(),
        )]),
        peer_verifiers: BTreeMap::from([]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };

    let results = do_attestation_exchange(client_config, server_config)?;

    assert_that!(
        results.client,
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );
    assert_that!(
        results.server,
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );

    Ok(())
}

#[googletest::test]
fn pairwise_incompatible_attestation_types_verification_fails() -> anyhow::Result<()> {
    let client_config = AttestationHandlerConfig {
        attestation_type: AttestationType::PeerUnidirectional,
        self_attesters: BTreeMap::from([]),
        self_endorsers: BTreeMap::from([]),
        peer_verifiers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_passing_mock_verifier(),
        )]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };
    let server_config = AttestationHandlerConfig {
        attestation_type: AttestationType::Bidirectional,
        self_attesters: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_attester(),
        )]),
        self_endorsers: BTreeMap::from([(
            MATCHED_ATTESTER_ID1.to_string(),
            create_mock_endorser(),
        )]),
        peer_verifiers: BTreeMap::from([(
            UNMATCHED_ATTESTER_ID.to_string(),
            create_passing_mock_verifier(),
        )]),
        attestation_results_aggregator: Box::new(DefaultVerifierResultsAggregator {}),
    };

    let results = do_attestation_exchange(client_config, server_config)?;

    assert_that!(
        results.client,
        ok(matches_pattern!(AttestationVerdict::AttestationPassed { .. }))
    );
    assert_that!(
        results.server,
        ok(matches_pattern!(AttestationVerdict::AttestationFailed {
            reason: "No matching attestation results",
            ..
        }))
    );

    Ok(())
}
