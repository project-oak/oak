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

use std::{
    collections::BTreeMap,
    string::{String, ToString},
};

use googletest::prelude::*;
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, AttestationResults, Endorsements, Evidence},
    session::v1::EndorsedEvidence,
};
use oak_session::{
    aggregators::{
        AggregatedVerificationError, DefaultLegacyVerifierResultsAggregator,
        LegacyVerifierResultsAggregator,
    },
    attestation::VerifierResult,
};

fn create_dummy_endorsed_evidence() -> EndorsedEvidence {
    EndorsedEvidence {
        evidence: Some(Evidence::default()),
        endorsements: Some(Endorsements::default()),
    }
}

fn create_passing_attestation_results() -> AttestationResults {
    AttestationResults { status: attestation_results::Status::Success.into(), ..Default::default() }
}

fn create_failing_attestation_results() -> AttestationResults {
    AttestationResults {
        status: attestation_results::Status::GenericFailure.into(),
        reason: String::from("Mock failure"),
        ..Default::default()
    }
}

const MATCHED_ATTESTER_ID1: &str = "MATCHED_ATTESTER_ID1";
const MATCHED_ATTESTER_ID2: &str = "MATCHED_ATTESTER_ID2";
const UNMATCHED_ATTESTER_ID: &str = "UNMATCHED_ATTESTER_ID";
const UNMATCHED_VERIFIER_ID: &str = "UNMATCHED_VERIFIER_ID";

#[googletest::test]
fn aggregated_attestation_succeeds() {
    let aggregator = DefaultLegacyVerifierResultsAggregator {};
    let attestation_results = BTreeMap::from([
        (
            MATCHED_ATTESTER_ID1.to_string(),
            VerifierResult::Success {
                evidence: create_dummy_endorsed_evidence(),
                result: create_passing_attestation_results(),
            },
        ),
        (
            MATCHED_ATTESTER_ID2.to_string(),
            VerifierResult::Success {
                evidence: create_dummy_endorsed_evidence(),
                result: create_passing_attestation_results(),
            },
        ),
    ]);
    assert_that!(aggregator.process_assertion_results(&attestation_results), ok(anything()));
}

#[googletest::test]
fn one_failed_verifier_aggregated_attestation_fails() {
    let aggregator = DefaultLegacyVerifierResultsAggregator {};
    let attestation_results = BTreeMap::from([
        (
            MATCHED_ATTESTER_ID1.to_string(),
            VerifierResult::Success {
                evidence: create_dummy_endorsed_evidence(),
                result: create_passing_attestation_results(),
            },
        ),
        (
            MATCHED_ATTESTER_ID2.to_string(),
            VerifierResult::Failure {
                evidence: create_dummy_endorsed_evidence(),
                result: create_failing_attestation_results(),
            },
        ),
    ]);
    assert_that!(
        aggregator.process_assertion_results(&attestation_results),
        err(matches_pattern!(AggregatedVerificationError::LegacyVerificationFailure { .. }))
    );
}

#[googletest::test]
fn unmatched_verifier_attestation_fails() {
    let aggregator = DefaultLegacyVerifierResultsAggregator {};
    let attestation_results: BTreeMap<String, VerifierResult> =
        BTreeMap::from([(UNMATCHED_VERIFIER_ID.to_string(), VerifierResult::Missing)]);

    assert_that!(
        aggregator.process_assertion_results(&attestation_results),
        err(matches_pattern!(AggregatedVerificationError::NoMatchedLegacyVerifier))
    );
}

#[googletest::test]
fn additional_attestation_passes() {
    let aggregator = DefaultLegacyVerifierResultsAggregator {};
    let attestation_results = BTreeMap::from([
        (
            MATCHED_ATTESTER_ID1.to_string(),
            VerifierResult::Success {
                evidence: create_dummy_endorsed_evidence(),
                result: create_passing_attestation_results(),
            },
        ),
        (
            UNMATCHED_ATTESTER_ID.to_string(),
            VerifierResult::Unverified { evidence: create_dummy_endorsed_evidence() },
        ),
    ]);
    assert_that!(aggregator.process_assertion_results(&attestation_results), ok(anything()));
}

#[googletest::test]
fn mix_successful_verifier_and_missing_passes() {
    let aggregator = DefaultLegacyVerifierResultsAggregator {};
    let attestation_results = BTreeMap::from([
        (
            MATCHED_ATTESTER_ID1.to_string(),
            VerifierResult::Success {
                evidence: create_dummy_endorsed_evidence(),
                result: create_passing_attestation_results(),
            },
        ),
        (UNMATCHED_VERIFIER_ID.to_string(), VerifierResult::Missing),
    ]);

    assert_that!(aggregator.process_assertion_results(&attestation_results), ok(anything()));
}
