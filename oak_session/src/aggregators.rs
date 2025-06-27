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

use alloc::{collections::BTreeMap, string::String, vec::Vec};

use oak_proto_rust::oak::attestation::v1::AttestationResults;

use crate::attestation::{AttestationVerdict, VerifierResult};

/// Defines the contract for aggregating multiple attestation results into a
/// single verdict.
///
/// In scenarios where multiple attestation mechanisms are used (identified by
/// different attestation IDs), an `VerifierResultsAggregator` determines the
/// overall success or failure of the attestation phase based on the individual
/// results.
pub trait VerifierResultsAggregator: Send {
    fn aggregate_attestation_results(
        &self,
        results: BTreeMap<String, VerifierResult>,
    ) -> AttestationVerdict;
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
pub struct DefaultVerifierResultsAggregator {}

impl VerifierResultsAggregator for DefaultVerifierResultsAggregator {
    /// Aggregates results based on the default policy: at least one result, and
    /// all must be successful.
    ///
    /// If `results` is empty, it returns `AttestationFailed` with a reason
    /// indicating no matching results. If any result in the `results` map
    /// has a `GenericFailure` status, it returns `AttestationFailed` with
    /// details of the failures. Otherwise, it returns `AttestationPassed`
    /// with the original results.
    fn aggregate_attestation_results(
        &self,
        results: BTreeMap<String, VerifierResult>,
    ) -> AttestationVerdict {
        let mut has_match = false;
        let mut has_configured_verifier = false;
        let mut failures: BTreeMap<&String, &AttestationResults> = BTreeMap::new();
        results.iter().for_each(|(id, v)| match v {
            VerifierResult::Success { .. } => {
                has_configured_verifier = true;
                has_match = true;
            }
            VerifierResult::Failure { result, .. } => {
                has_configured_verifier = true;
                has_match = true;
                failures.insert(id, result);
            }
            VerifierResult::Missing => has_configured_verifier = true,
            _ => {}
        });
        if has_configured_verifier && !has_match {
            return AttestationVerdict::AttestationFailed {
                reason: String::from("No matching evidence is provided"),
                attestation_results: results,
            };
        }
        if !failures.is_empty() {
            AttestationVerdict::AttestationFailed {
                reason: format!(
                    "Verification failed. {}",
                    failures
                        .iter()
                        .map(|(id, results)| format!("ID {}: {}", id, results.reason))
                        .collect::<Vec<String>>()
                        .join(";")
                ),
                attestation_results: results,
            }
        } else {
            AttestationVerdict::AttestationPassed { attestation_results: results }
        }
    }
}
