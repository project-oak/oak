//
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
//

use alloc::{collections::BTreeMap, string::String, sync::Arc};

use itertools::Itertools;
use thiserror::Error;

use crate::{
    attestation::VerifierResult,
    verifier::{
        BoundAssertionVerificationError, BoundAssertionVerifier, BoundAssertionVerifierResult,
    },
};

/// Represents verification errors.
#[derive(Error, Debug)]
pub enum AggregatedVerificationError {
    #[error("legacy attestation verification failed, failures: {failures:?}")]
    LegacyVerificationFailure { failures: BTreeMap<String, String> },
    #[error("assertion verification failed, failures: {failures:?}")]
    AssertionVerificationFailure { failures: BTreeMap<String, BoundAssertionVerificationError> },
    #[error("no matched legacy verifier found")]
    NoMatchedLegacyVerifier,
    #[error("no matched bound assertion verifier found")]
    NoMatchedBoundAssertionVerifier,
    #[error("aggregator configuration error")]
    ConfigurationError,
}

/// Defines the contract for aggregating multiple legacy attestation results
/// into a single verdict. Operates on the legacy attestation format using the
/// `EndorsedEvidence` proto to perform verification.
///
/// In scenarios where multiple attestation mechanisms are used (identified by
/// different attestation IDs), an `VerifierResultsAggregator` determines the
/// overall success or failure of the attestation phase based on the individual
/// results.
pub trait LegacyVerifierResultsAggregator: Send {
    /// Processes a map of attestation results and returns a single aggregated
    /// result.
    fn process_assertion_results(
        &self,
        results: &BTreeMap<String, VerifierResult>,
    ) -> Result<(), AggregatedVerificationError>;
}

/// A default implementation of the `VerifierResultsAggregator` trait.
///
/// This aggregator requires that:
/// 1. There is at least one attestation result provided.
/// 2. All provided attestation results indicate success.
///
/// It operates on the principle that only evidence matching a configured peer
/// verifier is considered, effectively performing an inner join between
/// expected verifiers and received evidence.
pub struct DefaultLegacyVerifierResultsAggregator {}

impl LegacyVerifierResultsAggregator for DefaultLegacyVerifierResultsAggregator {
    /// Aggregates results based on the default policy: at least one result, and
    /// all must be successful.
    ///
    /// If `results` is empty, it returns `AttestationFailed` with a reason
    /// indicating no matching results. If any result in the `results` map
    /// has a `GenericFailure` status, it returns `AttestationFailed` with
    /// details of the failures. Otherwise, it returns `AttestationPassed`
    /// with the original results.
    fn process_assertion_results(
        &self,
        results: &BTreeMap<String, VerifierResult>,
    ) -> Result<(), AggregatedVerificationError> {
        let mut has_match = false;
        let mut has_configured_verifier = false;
        let mut failures: BTreeMap<String, String> = BTreeMap::new();
        results.iter().for_each(|(id, v)| match v {
            VerifierResult::Success { .. } => {
                has_configured_verifier = true;
                has_match = true;
            }
            VerifierResult::Failure { result, .. } => {
                has_configured_verifier = true;
                has_match = true;
                failures.insert(id.clone(), result.reason.clone());
            }
            VerifierResult::Missing => has_configured_verifier = true,
            VerifierResult::Unverified { .. } => {}
        });
        if has_configured_verifier && !has_match {
            return Err(AggregatedVerificationError::NoMatchedLegacyVerifier);
        }
        if !failures.is_empty() {
            Err(AggregatedVerificationError::LegacyVerificationFailure { failures })
        } else {
            Ok(())
        }
    }
}

/// Defines the contract for aggregating multiple assertion verification results
/// into a single verdict. Evidence is supplied as `Assertion` protos.
///
/// In scenarios where multiple attestation mechanisms are used (identified by
/// different attestation IDs), an `VerifierResultsAggregator` determines the
/// overall success or failure of the attestation phase based on the individual
/// results.
pub trait AssertionResultsAggregator: Send {
    /// Processes a map of assertion verification results and returns a single
    /// aggregated result.
    fn process_assertion_results(
        &self,
        assertion_results: &BTreeMap<String, BoundAssertionVerifierResult>,
    ) -> Result<(), AggregatedVerificationError>;

    /// Checks whether the aggregator is compatible with the configured
    /// assertion verifiers (keyed by the attestation ID). The aggregators
    /// can define restrictions on the number of configured verifiers or on
    /// the particular attestation IDs.
    fn is_compatible_with_configuration(
        &self,
        peer_assertion_verifiers: &BTreeMap<String, Arc<dyn BoundAssertionVerifier>>,
    ) -> bool;
}

/// An [`AssertionResultsAggregator`] that succeeds if at least one assertion
/// verification is successful.
///
/// This aggregator implements a policy where the presence of any successful
/// verification result is sufficient to consider the entire attestation phase
/// successful. If no verifications succeed, it will fail.
pub struct Any {}

impl AssertionResultsAggregator for Any {
    fn process_assertion_results(
        &self,
        assertion_results: &BTreeMap<String, BoundAssertionVerifierResult>,
    ) -> Result<(), AggregatedVerificationError> {
        let mut failures: BTreeMap<String, BoundAssertionVerificationError> = BTreeMap::new();
        for (id, result) in assertion_results {
            match result {
                BoundAssertionVerifierResult::Success { .. } => return Ok(()),
                BoundAssertionVerifierResult::Failure { error, .. } => {
                    failures.insert(id.clone(), error.clone());
                }
                BoundAssertionVerifierResult::Missing
                | BoundAssertionVerifierResult::Unverified { .. } => {}
            }
        }

        if failures.is_empty() {
            Err(AggregatedVerificationError::NoMatchedBoundAssertionVerifier)
        } else {
            Err(AggregatedVerificationError::AssertionVerificationFailure { failures })
        }
    }

    fn is_compatible_with_configuration(
        &self,
        peer_assertion_verifiers: &BTreeMap<String, Arc<dyn BoundAssertionVerifier>>,
    ) -> bool {
        !peer_assertion_verifiers.is_empty()
    }
}

/// An [`AssertionResultsAggregator`] that succeeds only if all assertion
/// verifications are successful.
///
/// This aggregator enforces a strict policy where every configured assertion
/// verifier must report success. If any verification fails or is missing, the
/// entire attestation phase is considered failed.
pub struct All {}

impl AssertionResultsAggregator for All {
    fn process_assertion_results(
        &self,
        assertion_results: &BTreeMap<String, BoundAssertionVerifierResult>,
    ) -> Result<(), AggregatedVerificationError> {
        let mut failures: BTreeMap<String, BoundAssertionVerificationError> = BTreeMap::new();
        for (id, result) in assertion_results {
            match result {
                BoundAssertionVerifierResult::Success { .. } => {}
                BoundAssertionVerifierResult::Failure { error, .. } => {
                    failures.insert(id.clone(), error.clone());
                }
                BoundAssertionVerifierResult::Missing => {
                    failures
                        .insert(id.clone(), BoundAssertionVerificationError::PeerAssertionMissing);
                }
                BoundAssertionVerifierResult::Unverified { .. } => {}
            }
        }

        if !failures.is_empty() {
            Err(AggregatedVerificationError::AssertionVerificationFailure { failures })
        } else {
            Ok(())
        }
    }

    fn is_compatible_with_configuration(
        &self,
        peer_assertion_verifiers: &BTreeMap<String, Arc<dyn BoundAssertionVerifier>>,
    ) -> bool {
        !peer_assertion_verifiers.is_empty()
    }
}

/// An [`AssertionResultsAggregator`] that is intended to be used when exactly
/// one assertion verifier is configured.
///
/// This aggregator is designed for scenarios when only a single type of the
/// assertion based attestation is used. If more than one verifier is configured
/// and provides a result, this aggregator will return a configuration error.
/// For multiple attestation types the API user must pick a different
/// attestation (`All` or `Any`) or implement their own.
pub struct PassThrough {}

impl AssertionResultsAggregator for PassThrough {
    fn process_assertion_results(
        &self,
        assertion_results: &BTreeMap<String, BoundAssertionVerifierResult>,
    ) -> Result<(), AggregatedVerificationError> {
        // Pass through verifier only works if exactly one assertion verifier is
        // configured.
        match assertion_results
            .iter()
            .filter_map(|(id, result)| match result {
                BoundAssertionVerifierResult::Success { .. }
                | BoundAssertionVerifierResult::Failure { .. }
                | BoundAssertionVerifierResult::Missing => Some((id, result)),
                BoundAssertionVerifierResult::Unverified { .. } => None,
            })
            .exactly_one()
        {
            Ok((id, result)) => match result {
                BoundAssertionVerifierResult::Success { .. } => Ok(()),
                BoundAssertionVerifierResult::Failure { error, .. } => {
                    Err(AggregatedVerificationError::AssertionVerificationFailure {
                        failures: BTreeMap::from([(id.clone(), error.clone())]),
                    })
                }
                BoundAssertionVerifierResult::Missing => {
                    Err(AggregatedVerificationError::NoMatchedBoundAssertionVerifier)
                }
                BoundAssertionVerifierResult::Unverified { .. } => {
                    Err(AggregatedVerificationError::ConfigurationError)
                }
            },
            Err(_) => Err(AggregatedVerificationError::ConfigurationError),
        }
    }

    fn is_compatible_with_configuration(
        &self,
        peer_assertion_verifiers: &BTreeMap<String, Arc<dyn BoundAssertionVerifier>>,
    ) -> bool {
        !peer_assertion_verifiers.is_empty()
    }
}

/// An [`AssertionResultsAggregator`] for when no assertion verifiers are
/// configured.
///
/// This aggregator is used in configurations where no assertions are expected
/// from the peer. It will only succeed if there are no assertion verification
/// results to process. If any results are present, it indicates a
/// misconfiguration and will result in an error.
pub struct Empty {}

impl AssertionResultsAggregator for Empty {
    fn process_assertion_results(
        &self,
        assertion_results: &BTreeMap<String, BoundAssertionVerifierResult>,
    ) -> Result<(), AggregatedVerificationError> {
        assertion_results
            .iter()
            .all(|(_, result)| matches!(result, BoundAssertionVerifierResult::Unverified { .. }))
            .then_some(())
            .ok_or(AggregatedVerificationError::ConfigurationError)
    }

    fn is_compatible_with_configuration(
        &self,
        peer_assertion_verifiers: &BTreeMap<String, Arc<dyn BoundAssertionVerifier>>,
    ) -> bool {
        peer_assertion_verifiers.is_empty()
    }
}
