//
// Copyright 2024 The Project Oak Authors
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

//! This module provides implementations for the attestation phase of
//! establishing a secure session. Remote attestation is the process by which
//! two parties (e.g., a client and a server) exchange cryptographic evidence to
//! verify each other's identity, software configuration, and execution
//! environment. This establishes a root of trust before sensitive information
//! is exchanged or session keys are derived.
//!
//! ## Overview
//!
//! The attestation process involves one or both parties generating "evidence"
//! (often a quote from a secure hardware component like a TPM or SEV-SNP) and
//! "endorsements" (certificates or other data that vouch for the evidence).
//! This `EndorsedEvidence` is then sent to the peer, who verifies it against a
//! set of configured policies and trusted authorities.
//!
//! This module provides the building blocks to manage this exchange and
//! verification, supporting various configurations from unidirectional to
//! bidirectional attestation.
//!
//! ## Key Abstractions and Their Roles
//!
//! - **`AttestationType`**: An enum that defines the direction and necessity of
//!   attestation. This allows for flexibility:
//!     - `Bidirectional`: Both parties attest and verify each other.
//!     - `SelfUnidirectional`: Only "self" (the party configuring) attests to
//!       the peer.
//!     - `PeerUnidirectional`: Only the "peer" attests to "self".
//!     - `Unattested`: No attestation occurs (generally for testing or
//!       low-security scenarios).
//!
//! - **`AttestationProvider` Trait**: The core abstraction representing one
//!   party's role in the attestation process. Implementations
//!   (`ClientAttestationProvider`, `ServerAttestationProvider`) manage the
//!   state and logic for generating/sending their own evidence and/or
//!   receiving/verifying the peer's evidence. They use the `ProtocolEngine`
//!   trait to exchange `AttestRequest` and `AttestResponse` messages.
//!
//! - **`ClientAttestationProvider` / `ServerAttestationProvider`**: Concrete
//!   implementations for the client (initiator) and server (responder) roles.
//!   They are initialized with an `AttestationProviderConfig` which specifies:
//!     - `self_attesters`: Components that generate this party's attestation
//!       `Evidence`.
//!     - `self_endorsers`: Components that generate `Endorsements` for this
//!       party's `Evidence`.
//!     - `peer_verifiers`: A map of `AttestationVerifier`s used to verify the
//!       peer's `EndorsedEvidence`. Each verifier is associated with an
//!       "attestation ID" allowing multiple types of evidence to be processed.
//!     - `attestation_aggregator`: An `AttestationAggregator` that determines
//!       the overall outcome if multiple pieces of evidence are verified.
//!
//! - **`AttestationVerdict`**: An enum (`AttestationPassed` or
//!   `AttestationFailed`) representing the final outcome of the attestation
//!   process for a party. It's marked `#[must_use]` to ensure failures are
//!   explicitly handled. `AttestationPassed` includes the `AttestationResults`
//!   from successful verifications, which can be used later (e.g., for session
//!   binding).
//!
//! - **`AttestationAggregator` Trait (and `DefaultAttestationAggregator`)**:
//!   - **Purpose**: Defines how multiple individual `AttestationResults` (from
//!     verifying different pieces of peer evidence) are combined into a single
//!     `AttestationVerdict`.
//!   - **Why**: In complex systems, a peer might provide evidence from multiple
//!     sources (e.g., hardware attestation, software attestation). The
//!     aggregator decides if the overall attestation is successful based on a
//!     defined policy.
//!   - **`DefaultAttestationAggregator`**: Requires at least one piece of
//!     evidence to be successfully verified and all verified pieces to be
//!     successful.

use alloc::{collections::BTreeMap, string::String, sync::Arc};

use anyhow::{anyhow, Context, Error, Ok};
use itertools::{EitherOrBoth, Itertools};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, AttestationResults},
    session::v1::{AttestRequest, AttestResponse, EndorsedEvidence},
};

use crate::{config::AttestationProviderConfig, ProtocolEngine};

/// Represents the outcome of the attestation process.
///
/// This enum is marked `#[must_use]` to ensure that the `AttestationFailed`
/// variant is explicitly handled, preventing accidental ignoring of attestation
/// failures.
#[derive(Debug)]
#[must_use = "this `AttestationVerdict` may be an `AttestationFailed` variant, which should be handled"]
pub enum AttestationVerdict {
    /// Indicates that the attestation process completed successfully.
    ///
    /// Contains a map of `AttestationResults` for each attestation ID that
    /// was successfully verified. This map can be used by other parts of the
    /// session establishment process, for instance, to extract keys for session
    /// binding.
    AttestationPassed { attestation_results: BTreeMap<String, AttestationResults> },

    /// Indicates that the attestation process failed.
    ///
    /// Provides a general `reason` for the failure and a map of
    /// `error_messages` detailing failures for specific attestation IDs.
    AttestationFailed { reason: String, error_messages: BTreeMap<String, String> },
}

/// Defines the configuration for the attestation flow between two parties.
///
/// The terms "Self" and "Peer" are relative to the party configuring the
/// attestation. For a client, "Self" is the client and "Peer" is the server.
/// For a server, "Self" is the server and "Peer" is the client.
#[derive(Clone, Copy, Debug)]
pub enum AttestationType {
    /// Both parties perform attestation and verify each other's evidence.
    Bidirectional,
    /// "Self" attests its identity to the "Peer". The "Peer" verifies "Self".
    SelfUnidirectional,
    /// "Peer" attests its identity to "Self". "Self" verifies "Peer".
    PeerUnidirectional,
    /// No attestation is performed by either party. This is intended for
    /// testing and prototyping and is generally discouraged for production
    /// environments.
    Unattested,
}

/// Defines the contract for an attestation provider.
///
/// An `AttestationProvider` is responsible for managing the attestation process
/// for one side of the communication (either client or server). It handles the
/// generation or verification of attestation evidence. Implementations are
/// expected to be stateful, progressing as messages are exchanged.
pub trait AttestationProvider: Send {
    /// Retrieves the final attestation verdict once the process is complete.
    ///
    /// This method consumes the attestation result, meaning it can typically
    /// only be called once successfully. It returns an error if the
    /// attestation process is not yet finished or if the result has already
    /// been taken. The lifetime of the `AttestationVerdict` is tied to this
    /// consumption.
    fn take_attestation_result(self) -> Result<AttestationVerdict, Error>;
}

/// Defines the contract for aggregating multiple attestation results into a
/// single verdict.
///
/// In scenarios where multiple attestation mechanisms are used (identified by
/// different attestation IDs), an `AttestationAggregator` determines the
/// overall success or failure of the attestation phase based on the individual
/// results.
pub trait AttestationAggregator: Send {
    fn aggregate_attestation_results(
        &self,
        results: BTreeMap<String, AttestationResults>,
    ) -> AttestationVerdict;
}

/// A default implementation of the `AttestationAggregator` trait.
///
/// This aggregator requires that:
/// 1. There is at least one attestation result provided.
/// 2. All provided attestation results indicate success.
///
/// It operates on the principle that only evidence matching a configured peer
/// verifier is considered, effectively performing an inner join between
/// expected verifiers and received evidence.
pub struct DefaultAttestationAggregator {}

impl AttestationAggregator for DefaultAttestationAggregator {
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
        results: BTreeMap<String, AttestationResults>,
    ) -> AttestationVerdict {
        if results.is_empty() {
            return AttestationVerdict::AttestationFailed {
                reason: String::from("No matching attestation results"),
                error_messages: BTreeMap::new(),
            };
        }
        let failures: BTreeMap<&String, &AttestationResults> = results
            .iter()
            .filter(|(_, v)| v.status == attestation_results::Status::GenericFailure as i32)
            .collect();
        if !failures.is_empty() {
            AttestationVerdict::AttestationFailed {
                reason: String::from("Verification failed"),
                error_messages: failures
                    .iter()
                    .map(|(id, v)| ((*id).clone(), v.reason.clone()))
                    .collect(),
            }
        } else {
            AttestationVerdict::AttestationPassed { attestation_results: results }
        }
    }
}

/// Client-side implementation of the `AttestationProvider`.
///
/// This struct manages the attestation process for the client (the initiator of
/// the session). It generates an `AttestRequest` containing its own endorsed
/// evidence (if configured for `Bidirectional` or `SelfUnidirectional`
/// attestation) and processes the server's `AttestResponse` to verify peer
/// evidence (if configured for `Bidirectional` or `PeerUnidirectional`
/// attestation). It utilizes the `ProtocolEngine` trait to drive the message
/// exchange.
#[allow(dead_code)]
pub struct ClientAttestationProvider {
    config: AttestationProviderConfig,
    attest_request: Option<AttestRequest>,
    attestation_result: Option<AttestationVerdict>,
}

impl ClientAttestationProvider {
    /// Creates a new `ClientAttestationProvider` with the given configuration.
    ///
    /// Initializes the provider and, if applicable based on
    /// `config.attestation_type`, pre-generates the initial `AttestRequest`
    /// containing the client's own endorsed evidence. This evidence is
    /// created by invoking the `quote` method on configured
    /// `self_attesters` and `endorse` on `self_endorsers`.
    ///
    /// The lifetime of the attesters and endorsers in `config` must be managed
    /// by the caller; they are typically `Arc`ed to allow sharing.
    pub fn create(config: AttestationProviderConfig) -> Result<Self, Error> {
        Ok(Self {
            attest_request: Some(AttestRequest {
                endorsed_evidence: config
                    .self_attesters
                    .iter()
                    .map(|(id, attester)| {
                        let evidence = attester.quote()?;
                        // Adds endorsements with corresponding ID.
                        // Endorsements that don't have a corresponding Evidence will not be
                        // added to the `EndorsedEvidence`.
                        let endorsements = config
                            .self_endorsers
                            .get(id)
                            .map(|endorser| Ok(endorser.endorse(Some(&evidence))?))
                            .transpose()?;
                        let endorsed_evidence =
                            EndorsedEvidence { evidence: Some(evidence), endorsements };
                        Ok((id.clone(), endorsed_evidence))
                    })
                    .collect::<Result<BTreeMap<String, EndorsedEvidence>, Error>>()?,
            }),
            config,
            attestation_result: None,
        })
    }
}

impl AttestationProvider for ClientAttestationProvider {
    /// Retrieves the attestation verdict from the client's perspective.
    /// See `AttestationProvider::take_attestation_result` for details.
    fn take_attestation_result(mut self) -> Result<AttestationVerdict, Error> {
        self.attestation_result.take().ok_or(anyhow!("attestation is not complete"))
    }
}

impl ProtocolEngine<AttestResponse, AttestRequest> for ClientAttestationProvider {
    /// Gets the next outgoing `AttestRequest` message to be sent to the server.
    ///
    /// For the client, this is typically the initial `AttestRequest` containing
    /// its own evidence (if any). This method will return
    /// `Some(AttestRequest)` once, after which it will return `Ok(None)` as
    /// the client sends only one attestation message.
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<AttestRequest>> {
        Ok(self.attest_request.take())
    }

    /// Processes an incoming `AttestResponse` message from the server.
    ///
    /// This method is called when the client receives the server's attestation
    /// data. It verifies the server's evidence based on the configured
    /// `peer_verifiers` and `attestation_type`. The result of this
    /// verification is stored internally and can be retrieved via
    /// `take_attestation_result`.
    ///
    /// Returns `Ok(Some(()))` if the message was processed and the attestation
    /// step is now complete from the client's perspective regarding message
    /// exchange. Returns `Ok(None)` if the attestation result was already
    /// obtained, indicating no further messages are expected in this phase.
    fn put_incoming_message(
        &mut self,
        incoming_message: AttestResponse,
    ) -> anyhow::Result<Option<()>> {
        if self.attestation_result.is_some() {
            // Attestation result is already obtained - no new messages expected.
            return Ok(None);
        }
        self.attestation_result = match self.config.attestation_type {
            AttestationType::Bidirectional | AttestationType::PeerUnidirectional => {
                Some(self.config.attestation_aggregator.aggregate_attestation_results(
                    combine_attestation_results(
                        &self.config.peer_verifiers,
                        &incoming_message.endorsed_evidence,
                    )?,
                ))
            }
            AttestationType::SelfUnidirectional | AttestationType::Unattested => {
                Some(AttestationVerdict::AttestationPassed { attestation_results: BTreeMap::new() })
            }
        };
        Ok(Some(()))
    }
}

/// Server-side implementation of the `AttestationProvider`.
///
/// This struct manages the attestation process for the server (the responder in
/// the session). It processes the client's `AttestRequest` to verify client
/// evidence (if configured for `Bidirectional` or `PeerUnidirectional`
/// attestation) and generates an `AttestResponse` containing its own endorsed
/// evidence (if configured for `Bidirectional` or `SelfUnidirectional`
/// attestation). It utilizes the `ProtocolEngine` trait to drive the message
/// exchange.
#[allow(dead_code)]
pub struct ServerAttestationProvider {
    config: AttestationProviderConfig,
    attest_response: Option<AttestResponse>,
    attestation_result: Option<AttestationVerdict>,
}

impl ServerAttestationProvider {
    /// Creates a new `ServerAttestationProvider` with the given configuration.
    ///
    /// Initializes the provider and, if applicable based on
    /// `config.attestation_type`, pre-generates the `AttestResponse`
    /// containing the server's own endorsed evidence. This evidence is
    /// created by invoking the `quote` method on configured
    /// `self_attesters` and `endorse` on `self_endorsers`.
    ///
    /// The lifetime of the attesters and endorsers in `config` must be managed
    /// by the caller.
    pub fn create(config: AttestationProviderConfig) -> Result<Self, Error> {
        Ok(Self {
            attest_response: Some(AttestResponse {
                endorsed_evidence: config
                    .self_attesters
                    .iter()
                    .map(|(id, attester)| {
                        let evidence = attester.quote()?;
                        // Adds endorsements with corresponding ID.
                        // Endorsements that don't have a corresponding Evidence will not be
                        // added to the `EndorsedEvidence`.
                        let endorsements = config
                            .self_endorsers
                            .get(id)
                            .map(|endorser| Ok(endorser.endorse(Some(&evidence))?))
                            .transpose()?;
                        let endorsed_evidence =
                            EndorsedEvidence { evidence: Some(evidence), endorsements };
                        Ok((id.clone(), endorsed_evidence))
                    })
                    .collect::<Result<BTreeMap<String, EndorsedEvidence>, Error>>()?,
            }),
            config,
            attestation_result: None,
        })
    }
}

impl AttestationProvider for ServerAttestationProvider {
    /// Retrieves the attestation verdict from the server's perspective.
    /// See `AttestationProvider::take_attestation_result` for details.
    fn take_attestation_result(mut self) -> Result<AttestationVerdict, Error> {
        self.attestation_result.take().ok_or(anyhow!("attestation is not complete"))
    }
}

impl ProtocolEngine<AttestRequest, AttestResponse> for ServerAttestationProvider {
    /// Gets the next outgoing `AttestResponse` message to be sent to the
    /// client.
    ///
    /// For the server, this is typically the `AttestResponse` generated after
    /// processing the client's request (or pre-generated if only
    /// self-attesting). This method will return `Some(AttestResponse)`
    /// once, after which it will return `Ok(None)`.
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<AttestResponse>> {
        Ok(self.attest_response.take())
    }

    /// Processes an incoming `AttestRequest` message from the client.
    ///
    /// This method is called when the server receives the client's attestation
    /// data. It verifies the client's evidence based on the configured
    /// `peer_verifiers` and `attestation_type`. The result of this
    /// verification is stored internally and can be retrieved via
    /// `take_attestation_result`.
    ///
    /// Returns `Ok(Some(()))` if the message was processed. The server then
    /// typically prepares its own `AttestResponse`.
    /// Returns `Ok(None)` if the attestation result was already obtained.
    fn put_incoming_message(
        &mut self,
        incoming_message: AttestRequest,
    ) -> anyhow::Result<Option<()>> {
        if self.attestation_result.is_some() {
            // Attestation result is already obtained - no new messages expected.
            return Ok(None);
        }
        self.attestation_result = match self.config.attestation_type {
            AttestationType::Bidirectional | AttestationType::PeerUnidirectional => {
                Some(self.config.attestation_aggregator.aggregate_attestation_results(
                    combine_attestation_results(
                        &self.config.peer_verifiers,
                        &incoming_message.endorsed_evidence,
                    )?,
                ))
            }
            AttestationType::SelfUnidirectional | AttestationType::Unattested => {
                Some(AttestationVerdict::AttestationPassed { attestation_results: BTreeMap::new() })
            }
        };
        Ok(Some(()))
    }
}

/// Combines received `attested_evidence` with configured `verifiers`.
///
/// This function performs a merge-join between the set of verifiers (keyed by
/// attestation ID) and the set of received endorsed evidence (also keyed by
/// attestation ID). For each matching pair, it invokes the `verify` method of
/// the `AttestationVerifier`.
///
/// It effectively filters the `attested_evidence` to only include entries for
/// which a corresponding verifier is configured, and then collects their
/// verification outcomes.
///
/// Returns a map of `AttestationResults` keyed by attestation ID for all
/// successfully processed (though not necessarily successfully verified)
/// evidence.
fn combine_attestation_results(
    verifiers: &BTreeMap<String, Arc<dyn AttestationVerifier>>,
    attested_evidence: &BTreeMap<String, EndorsedEvidence>,
) -> Result<BTreeMap<String, AttestationResults>, Error> {
    let verifiable_evidence = verifiers
        .iter()
        .merge_join_by(attested_evidence.iter(), |(id1, _), (id2, _)| Ord::cmp(id1, id2))
        .filter_map(|v| match v {
            EitherOrBoth::Both((id, verifier), (_, e)) => Some((id, (verifier, e))),
            _ => None,
        });
    let mut attestation_results = BTreeMap::new();
    for (id, (verifier, e)) in verifiable_evidence {
        attestation_results.insert(
            id.clone(),
            verifier.verify(
                e.evidence
                    .as_ref()
                    .context(format!("Missing evidence in the attest response for ID {}", id))?,
                e.endorsements.as_ref().context(format!(
                    "Missing endorsements in the attest response for ID {}",
                    id
                ))?,
            )?,
        );
    }
    Ok(attestation_results)
}
