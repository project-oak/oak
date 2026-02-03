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
//! - **`AttestationHandler` Trait**: The core abstraction representing one
//!   party's role in the attestation process. Implementations
//!   (`ClientAttestationHandler`, `ServerAttestationHandler`) manage the state
//!   and logic for generating/sending their own evidence and/or
//!   receiving/verifying the peer's evidence. They use the `ProtocolEngine`
//!   trait to exchange `AttestRequest` and `AttestResponse` messages.
//!
//! - **`ClientAttestationHandler` / `ServerAttestationHandler`**: Concrete
//!   implementations for the client (initiator) and server (responder) roles.
//!   They are initialized with an `AttestationHandlerConfig` which specifies:
//!     - `self_attesters`: Components that generate this party's attestation
//!       `Evidence`.
//!     - `self_endorsers`: Components that generate `Endorsements` for this
//!       party's `Evidence`.
//!     - `peer_verifiers`: A map of `AttestationVerifier`s used to verify the
//!       peer's `EndorsedEvidence`. Each verifier is associated with an
//!       "attestation ID" allowing multiple types of evidence to be processed.
//!     - `attestation_aggregator`: An `VerifierResultsAggregator` that
//!       determines the overall outcome if multiple pieces of evidence are
//!       verified.
//!
//! - **`PeerAttestationVerdict`**: An enum (`AttestationPassed` or
//!   `AttestationFailed`) representing the final outcome of the attestation
//!   process for a party. It's marked `#[must_use]` to ensure failures are
//!   explicitly handled. `AttestationPassed` includes the `AttestationResults`
//!   from successful verifications, which can be used later (e.g., for session
//!   binding).
//!
//! - **`VerifierResultsAggregator` Trait (and
//!   `DefaultVerifierResultsAggregator`)**:
//!   - **Purpose**: Defines how multiple individual `AttestationResults` (from
//!     verifying different pieces of peer evidence) are combined into a single
//!     `AttestationVerdict`.
//!   - **Why**: In complex systems, a peer might provide evidence from multiple
//!     sources (e.g., hardware attestation, software attestation). The
//!     aggregator decides if the overall attestation is successful based on a
//!     defined policy.
//!   - **`DefaultVerifierResultsAggregator`**: Requires at least one piece of
//!     evidence to be successfully verified and all verified pieces to be
//!     successful.

use alloc::{
    boxed::Box,
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};

use anyhow::{Error, anyhow};
use itertools::{EitherOrBoth, Itertools};
use oak_proto_rust::oak::{
    attestation::v1::{Assertion, AttestationResults, attestation_results},
    session::v1::{AttestRequest, AttestResponse, EndorsedEvidence},
};
use prost::Message;

use crate::{
    ProtocolEngine,
    aggregators::AggregatedVerificationError,
    config::{AttestationHandlerConfig, PeerAttestationVerifier},
    generator::BindableAssertion,
    session_binding::SessionBindingVerifier,
    verifier::{BoundAssertionVerifier, BoundAssertionVerifierResult},
};

/// Represents the outcome of the attestation process.
///
/// This enum is marked `#[must_use]` to ensure that the `AttestationFailed`
/// variant is explicitly handled, preventing accidental ignoring of attestation
/// failures.
#[must_use = "this `PeerAttestationVerdict` may be an `AttestationFailed` variant, which should be handled"]
#[derive(Debug)]
pub enum PeerAttestationVerdict {
    /// Indicates that the attestation process completed successfully.
    ///
    /// Contains a map of VerifierResult instances for each attestation ID that
    /// was successfully verified. This map can be used by other parts of the
    /// session establishment process, for instance, to extract keys for session
    /// binding.
    AttestationPassed {
        legacy_verification_results: BTreeMap<String, VerifierResult>,
        assertion_verification_results: BTreeMap<String, BoundAssertionVerifierResult>,
    },

    /// Indicates that the attestation process failed.
    ///
    /// Provides a general `reason` for the failure and a map of
    /// `attestation_results` for specific attestation IDs for further details.
    AttestationFailed {
        reason: String,
        legacy_verification_results: BTreeMap<String, VerifierResult>,
        assertion_verification_results: BTreeMap<String, BoundAssertionVerifierResult>,
    },
}

impl PeerAttestationVerdict {
    /// Retrieves the underlying individual attestation results from the
    /// attestation verdict. Results can be retrieved whether the overall
    /// attestation verdict is pass or fail.
    pub fn get_legacy_verification_results(&self) -> &BTreeMap<String, VerifierResult> {
        match self {
            PeerAttestationVerdict::AttestationPassed { legacy_verification_results, .. } => {
                legacy_verification_results
            }
            PeerAttestationVerdict::AttestationFailed { legacy_verification_results, .. } => {
                legacy_verification_results
            }
        }
    }

    /// Retrieves the underlying individual assertion verification results from
    /// the attestation verdict. Results can be retrieved whether the
    /// overall attestation verdict is pass or fail.
    pub fn get_assertion_verification_results(
        &self,
    ) -> &BTreeMap<String, BoundAssertionVerifierResult> {
        match self {
            PeerAttestationVerdict::AttestationPassed {
                assertion_verification_results, ..
            } => assertion_verification_results,
            PeerAttestationVerdict::AttestationFailed {
                assertion_verification_results, ..
            } => assertion_verification_results,
        }
    }

    /// Checks whether any evidence or assertions were provided by the peer that
    /// would require session binding.
    ///
    /// This is true if any of the verification results are not in the `Missing`
    /// state, which implies that some form of attestation was attempted.
    pub fn needs_session_bindings(&self) -> bool {
        self.get_assertion_verification_results().iter().any(|(_, v)| match v {
            BoundAssertionVerifierResult::Success { .. }
            | BoundAssertionVerifierResult::Failure { .. }
            | BoundAssertionVerifierResult::Unverified { .. } => true,
            BoundAssertionVerifierResult::Missing => false,
        }) | self.get_legacy_verification_results().iter().any(|(_, v)| match v {
            VerifierResult::Success { .. }
            | VerifierResult::Failure { .. }
            | VerifierResult::Unverified { .. } => true,
            VerifierResult::Missing => false,
        })
    }
}

/// Holds the results of the attestation exchange from the perspective of one of
/// the parties.
///
/// This struct is created at the end of the attestation process and contains
/// the verdict on the peer's attestation, any assertions made by this party,
/// and a binding token to link the attestation to the cryptographic session.
pub struct AttestationState {
    /// The outcome of verifying the peer's attestation evidence.
    pub peer_attestation_verdict: PeerAttestationVerdict,
    /// Assertions made by this party, which can be bound to the session.
    ///
    /// These are generated by the configured `AssertionGenerator`s and sent to
    /// the peer.
    pub self_assertions: BTreeMap<String, Box<dyn BindableAssertion>>,
    /// Verifiers for session bindings provided by the peer.
    ///
    /// These are created from successfully verified peer attestation evidence.
    pub peer_session_binding_verifiers: BTreeMap<String, Box<dyn SessionBindingVerifier>>,
    /// A token derived from the attestation exchange, intended to be used to
    /// cryptographically bind the session keys to the attestation results.
    pub attestation_binding_token: Vec<u8>,
}

/// Defines the configuration for the attestation flow between two parties.
///
/// The terms "Self" and "Peer" are relative to the party configuring the
/// attestation. For a client, "Self" is the client and "Peer" is the server.
/// For a server, "Self" is the server and "Peer" is the client.
#[derive(Clone, Copy, Debug, PartialEq)]
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

/// Verification result for an individual verifier (per attestation type)
#[derive(Clone, Debug, PartialEq)]
pub enum VerifierResult {
    // Verifier yielded a success result
    Success { evidence: EndorsedEvidence, result: AttestationResults },
    // Verifier returned a failure
    Failure { evidence: EndorsedEvidence, result: AttestationResults },
    // No evidence have been supplied for the verifier
    Missing,
    // The evidence has been presented but no verifier is confiugured
    Unverified { evidence: EndorsedEvidence },
}

/// Defines the contract for an attestation handler.
///
/// An `AttestationHandler` is responsible for managing the attestation process
/// for one side of the communication (either client or server). It handles the
/// generation or verification of attestation evidence. Implementations are
/// expected to be stateful, progressing as messages are exchanged.
pub trait AttestationHandler: Send {
    /// Retrieves the final attestation state once the process is complete.
    ///
    /// This method consumes the attestation state, meaning it can
    /// only be called once by design. It returns an error if the
    /// attestation process is not yet finished.
    fn take_attestation_state(self) -> Result<AttestationState, Error>;
}

/// Client-side implementation of the `AttestationHandler`.
///
/// This struct manages the attestation process for the client (the initiator of
/// the session). It generates an `AttestRequest` containing its own endorsed
/// evidence (if configured for `Bidirectional` or `SelfUnidirectional`
/// attestation) and processes the server's `AttestResponse` to verify peer
/// evidence (if configured for `Bidirectional` or `PeerUnidirectional`
/// attestation). It utilizes the `ProtocolEngine` trait to drive the message
/// exchange.
#[allow(dead_code)]
pub struct ClientAttestationHandler {
    config: AttestationHandlerConfig,
    attest_request: Option<AttestRequest>,
    attestation_result: Option<PeerAttestationVerdict>,
    bindable_assertions: BTreeMap<String, Box<dyn BindableAssertion>>,
    attestation_binding_token: Vec<u8>,
}

impl ClientAttestationHandler {
    /// Creates a new `ClientAttestationHandler` with the given configuration.
    ///
    /// Initializes the provider and, if applicable based on
    /// `config.attestation_type`, pre-generates the initial `AttestRequest`
    /// containing the client's own endorsed evidence. This evidence is
    /// created by invoking the `quote` method on configured
    /// `self_attesters` and `endorse` on `self_endorsers`.
    ///
    /// The lifetime of the attesters and endorsers in `config` must be managed
    /// by the caller; they are typically `Arc`ed to allow sharing.
    pub fn create(config: AttestationHandlerConfig) -> Result<Self, Error> {
        let bindable_assertions = config
            .self_assertion_generators
            .iter()
            .map(|(id, assertion_generator)| Ok((id.clone(), assertion_generator.generate()?)))
            .collect::<anyhow::Result<BTreeMap<String, Box<dyn BindableAssertion>>>>()?;
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
                            .map(|endorser| endorser.endorse(Some(&evidence)))
                            .transpose()?;
                        let endorsed_evidence =
                            EndorsedEvidence { evidence: Some(evidence), endorsements };
                        Ok((id.clone(), endorsed_evidence))
                    })
                    .collect::<Result<BTreeMap<String, EndorsedEvidence>, Error>>()?,
                assertions: bindable_assertions
                    .iter()
                    .map(|(id, bindable_assertion)| {
                        (id.clone(), bindable_assertion.assertion().clone())
                    })
                    .collect(),
            }),
            bindable_assertions,
            config,
            attestation_result: None,
            attestation_binding_token: Vec::new(),
        })
    }
}

impl AttestationHandler for ClientAttestationHandler {
    /// Retrieves the attestation state from the client's perspective.
    /// See `AttestationHandler::take_attestation_state` for details.
    fn take_attestation_state(mut self) -> Result<AttestationState, Error> {
        let verdict =
            self.attestation_result.take().ok_or(anyhow!("attestation is not complete"))?;
        let verification_results = verdict.get_legacy_verification_results();
        let peer_session_binding_verifiers = verification_results.iter().filter_map(|(id, result)| {
                match result {
                    // Session binding verifiers can only be created from successfully verified evidence.
                    VerifierResult::Success { result, .. } => {
                        let peer_verifier: &PeerAttestationVerifier = self.config.peer_verifiers.get(id)
                            .expect("no peer verifier for already succesfully verified evidence: it cannot happen");
                        match peer_verifier.binding_verifier_provider.create_session_binding_verifier(result) {
                            core::result::Result::Ok(binding_verifier) => Some(Ok((id.clone(), binding_verifier))),
                            Err(err) => Some(Err(err)),
                        }
                    },
                    _ => None,
                }
            }).collect::<Result<BTreeMap<String, Box<dyn SessionBindingVerifier>>, Error>>()?;
        Ok(AttestationState {
            peer_session_binding_verifiers,
            peer_attestation_verdict: verdict,
            self_assertions: self.bindable_assertions,
            attestation_binding_token: self.attestation_binding_token,
        })
    }
}

impl ProtocolEngine<AttestResponse, AttestRequest> for ClientAttestationHandler {
    /// Gets the next outgoing `AttestRequest` message to be sent to the server.
    ///
    /// For the client, this is typically the initial `AttestRequest` containing
    /// its own evidence (if any). This method will return
    /// `Some(AttestRequest)` once, after which it will return `Ok(None)` as
    /// the client sends only one attestation message.
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<AttestRequest>> {
        self.attestation_binding_token.extend(serialize_assertions(
            &self
                .bindable_assertions
                .iter()
                .map(|(id, bindable_assertion)| {
                    (id.clone(), bindable_assertion.assertion().clone())
                })
                .collect(),
        ));
        Ok(self.attest_request.take())
    }

    /// Processes an incoming `AttestResponse` message from the server.
    ///
    /// This method is called when the client receives the server's attestation
    /// data. It verifies the server's evidence based on the configured
    /// `peer_verifiers` and `attestation_type`. The result of this
    /// verification is stored internally and can be retrieved via
    /// `take_attestation_state`.
    ///
    /// Returns `Ok(Some(()))` if the message was processed and the attestation
    /// step is now complete from the client's perspective regarding message
    /// exchange. Returns `Ok(None)` if the attestation result was already
    /// obtained, indicating no further messages are expected in this phase.
    fn put_incoming_message(
        &mut self,
        incoming_message: AttestResponse,
    ) -> anyhow::Result<Option<()>> {
        self.attestation_binding_token.extend(serialize_assertions(&incoming_message.assertions));

        if self.attestation_result.is_some() {
            // Attestation result is already obtained - no new messages expected.
            return Ok(None);
        }
        let legacy_results = combine_attestation_results(
            &self.config.peer_verifiers,
            incoming_message.endorsed_evidence,
        )?;
        let assertion_results = combine_assertion_results(
            &self.config.peer_assertion_verifiers,
            incoming_message.assertions,
        );
        self.attestation_result = Some(combine_legacy_and_assertion_aggregated_verification(
            self.config
                .legacy_attestation_results_aggregator
                .process_assertion_results(&legacy_results),
            self.config
                .assertion_attestation_aggregator
                .process_assertion_results(&assertion_results),
            legacy_results,
            assertion_results,
        ));
        Ok(Some(()))
    }
}

/// Server-side implementation of the `AttestationHandler`.
///
/// This struct manages the attestation process for the server (the responder in
/// the session). It processes the client's `AttestRequest` to verify client
/// evidence (if configured for `Bidirectional` or `PeerUnidirectional`
/// attestation) and generates an `AttestResponse` containing its own endorsed
/// evidence (if configured for `Bidirectional` or `SelfUnidirectional`
/// attestation). It utilizes the `ProtocolEngine` trait to drive the message
/// exchange.
#[allow(dead_code)]
pub struct ServerAttestationHandler {
    config: AttestationHandlerConfig,
    attest_response: Option<AttestResponse>,
    attestation_result: Option<PeerAttestationVerdict>,
    bindable_assertions: BTreeMap<String, Box<dyn BindableAssertion>>,
    attestation_binding_token: Vec<u8>,
}

impl ServerAttestationHandler {
    /// Creates a new `ServerAttestationHandler` with the given configuration.
    ///
    /// Initializes the provider and, if applicable based on
    /// `config.attestation_type`, pre-generates the `AttestResponse`
    /// containing the server's own endorsed evidence. This evidence is
    /// created by invoking the `quote` method on configured
    /// `self_attesters` and `endorse` on `self_endorsers`.
    ///
    /// The lifetime of the attesters and endorsers in `config` must be managed
    /// by the caller.
    pub fn create(config: AttestationHandlerConfig) -> Result<Self, Error> {
        let bindable_assertions = config
            .self_assertion_generators
            .iter()
            .map(|(id, assertion_generator)| Ok((id.clone(), assertion_generator.generate()?)))
            .collect::<anyhow::Result<BTreeMap<String, Box<dyn BindableAssertion>>>>()?;
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
                            .map(|endorser| endorser.endorse(Some(&evidence)))
                            .transpose()?;
                        let endorsed_evidence =
                            EndorsedEvidence { evidence: Some(evidence), endorsements };
                        Ok((id.clone(), endorsed_evidence))
                    })
                    .collect::<Result<BTreeMap<String, EndorsedEvidence>, Error>>()?,
                assertions: bindable_assertions
                    .iter()
                    .map(|(id, bindable_assertion)| {
                        (id.clone(), bindable_assertion.assertion().clone())
                    })
                    .collect(),
            }),
            bindable_assertions,
            config,
            attestation_result: None,
            attestation_binding_token: Vec::new(),
        })
    }
}

impl AttestationHandler for ServerAttestationHandler {
    /// Retrieves the attestation state from the server's perspective.
    /// See `AttestationHandler::take_attestation_state` for details.
    fn take_attestation_state(mut self) -> Result<AttestationState, Error> {
        let verdict =
            self.attestation_result.take().ok_or(anyhow!("attestation is not complete"))?;
        let verification_results = verdict.get_legacy_verification_results();
        let peer_session_binding_verifiers = verification_results.iter().filter_map(|(id, result)| {
                match result {
                    // Session binding verifiers can only be created from successfully verified evidence.
                    VerifierResult::Success { result, .. } => {
                        let peer_verifier: &PeerAttestationVerifier = self.config.peer_verifiers.get(id)
                            .expect("no peer verifier for already succesfully verified evidence: it cannot happen");
                        match peer_verifier.binding_verifier_provider.create_session_binding_verifier(result) {
                            core::result::Result::Ok(binding_verifier) => Some(Ok((id.clone(), binding_verifier))),
                            Err(err) => Some(Err(err)),
                        }
                    },
                    _ => None,
                }
            }).collect::<Result<BTreeMap<String, Box<dyn SessionBindingVerifier>>, Error>>()?;
        Ok(AttestationState {
            peer_session_binding_verifiers,
            peer_attestation_verdict: verdict,
            self_assertions: self.bindable_assertions,
            attestation_binding_token: self.attestation_binding_token,
        })
    }
}

impl ProtocolEngine<AttestRequest, AttestResponse> for ServerAttestationHandler {
    /// Gets the next outgoing `AttestResponse` message to be sent to the
    /// client.
    ///
    /// For the server, this is typically the `AttestResponse` generated after
    /// processing the client's request (or pre-generated if only
    /// self-attesting). This method will return `Some(AttestResponse)`
    /// once, after which it will return `Ok(None)`.
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<AttestResponse>> {
        self.attestation_binding_token.extend(serialize_assertions(
            &self
                .bindable_assertions
                .iter()
                .map(|(id, bindable_assertion)| {
                    (id.clone(), bindable_assertion.assertion().clone())
                })
                .collect(),
        ));
        Ok(self.attest_response.take())
    }

    /// Processes an incoming `AttestRequest` message from the client.
    ///
    /// This method is called when the server receives the client's attestation
    /// data. It verifies the client's evidence based on the configured
    /// `peer_verifiers` and `attestation_type`. The result of this
    /// verification is stored internally and can be retrieved via
    /// `take_attestation_state`.
    ///
    /// Returns `Ok(Some(()))` if the message was processed. The server then
    /// typically prepares its own `AttestResponse`.
    /// Returns `Ok(None)` if the attestation result was already obtained.
    fn put_incoming_message(
        &mut self,
        incoming_message: AttestRequest,
    ) -> anyhow::Result<Option<()>> {
        self.attestation_binding_token.extend(serialize_assertions(&incoming_message.assertions));
        if self.attestation_result.is_some() {
            // Attestation result is already obtained - no new messages expected.
            return Ok(None);
        }
        let legacy_results = combine_attestation_results(
            &self.config.peer_verifiers,
            incoming_message.endorsed_evidence,
        )?;
        let assertion_results = combine_assertion_results(
            &self.config.peer_assertion_verifiers,
            incoming_message.assertions,
        );
        self.attestation_result = Some(combine_legacy_and_assertion_aggregated_verification(
            self.config
                .legacy_attestation_results_aggregator
                .process_assertion_results(&legacy_results),
            self.config
                .assertion_attestation_aggregator
                .process_assertion_results(&assertion_results),
            legacy_results,
            assertion_results,
        ));
        Ok(Some(()))
    }
}

/// Combines received `attested_evidence` with configured `verifiers`.
///
/// This function performs a merge-join between the set of verifiers (keyed by
/// attestation ID) and the set of received endorsed evidence (also keyed by
/// attestation ID). For each matching pair, it invokes the `verify` method of
/// the `AttestationVerifier`. For unmatched verifiers or evidence it creates a
/// `VerifierResult::Missing` or `VerifierResult::Unverified` result
/// respectively.`
///
/// Returns a map of `VerifierResult` keyed by attestation ID.
fn combine_attestation_results(
    verifiers: &BTreeMap<String, PeerAttestationVerifier>,
    attested_evidence: BTreeMap<String, EndorsedEvidence>,
) -> Result<BTreeMap<String, VerifierResult>, Error> {
    verifiers
        .iter()
        .merge_join_by(attested_evidence, |(id1, _), (id2, _)| Ord::cmp(id1, &id2))
        .map(|v| match v {
            EitherOrBoth::Both((_, peer_verifier), (id, ee)) => {
                match (ee.evidence.as_ref(), ee.endorsements.as_ref()) {
                    (Some(evidence), Some(endorsements)) => {
                        let result = peer_verifier.verifier.verify(evidence, endorsements)?;
                        Ok((
                            id,
                            match result.status() {
                                attestation_results::Status::Success => {
                                    VerifierResult::Success { evidence: ee, result }
                                }
                                _ => VerifierResult::Failure { evidence: ee, result },
                            },
                        ))
                    }
                    _ => Ok((
                        id,
                        VerifierResult::Failure {
                            evidence: ee,
                            result: AttestationResults {
                                status: attestation_results::Status::GenericFailure.into(),
                                reason: "Both evidence and endorsements need to be provided"
                                    .to_string(),
                                ..Default::default()
                            },
                        },
                    )),
                }
            }
            EitherOrBoth::Left((id, _)) => Ok((id.clone(), VerifierResult::Missing)),
            EitherOrBoth::Right((id, evidence)) => {
                Ok((id, VerifierResult::Unverified { evidence }))
            }
        })
        .collect::<Result<BTreeMap<String, VerifierResult>, Error>>()
}

/// Combines received `assertions` with configured
/// `assertion_verifiers`.
///
/// This function performs a merge-join between the set of verifiers (keyed by
/// ID) and the set of received assertions (also keyed by ID). For
/// each matching pair, it invokes the `verify` method of the
/// `AsertionVerifier`. For unmatched verifiers or evidence it creates a
/// `BoundAssertionVerifierResult::Missing` or
/// `BoundAssertionVerifierResult::Unverified` result respectively.`
///
/// Returns a map of `BoundAssertionVerifierResult` keyed by ID for all
/// successfully processed (though not necessarily successfully verified)
/// evidence.
fn combine_assertion_results(
    assertion_verifiers: &BTreeMap<String, Arc<dyn BoundAssertionVerifier>>,
    assertions: BTreeMap<String, Assertion>,
) -> BTreeMap<String, BoundAssertionVerifierResult> {
    assertion_verifiers
        .iter()
        .merge_join_by(assertions, |(id1, _), (id2, _)| Ord::cmp(id1, &id2))
        .map(|v| match v {
            EitherOrBoth::Both((id, verifier), (_, assertion)) => {
                match verifier.verify_assertion(&assertion) {
                    Ok(verified_bound_assertion) => (
                        id.clone(),
                        BoundAssertionVerifierResult::Success { verified_bound_assertion },
                    ),
                    Err(error) => {
                        (id.clone(), BoundAssertionVerifierResult::Failure { assertion, error })
                    }
                }
            }
            EitherOrBoth::Left((id, _)) => (id.clone(), BoundAssertionVerifierResult::Missing),
            EitherOrBoth::Right((id, assertion)) => {
                (id.clone(), BoundAssertionVerifierResult::Unverified { assertion })
            }
        })
        .collect()
}

/// Combines the aggregated results of legacy and assertion-based verification
/// into a single verdict.
///
/// If both legacy and assertion verification succeed, it returns
/// `AttestationPassed`. If either fails, it returns `AttestationFailed` with a
/// reason string detailing the failure(s). The detailed results for both are
/// included in the verdict regardless of the outcome.
fn combine_legacy_and_assertion_aggregated_verification(
    legacy_result: Result<(), AggregatedVerificationError>,
    assertion_result: Result<(), AggregatedVerificationError>,
    legacy_verification_results: BTreeMap<String, VerifierResult>,
    assertion_verification_results: BTreeMap<String, BoundAssertionVerifierResult>,
) -> PeerAttestationVerdict {
    match (legacy_result, assertion_result) {
        (Ok(()), Ok(())) => PeerAttestationVerdict::AttestationPassed {
            legacy_verification_results,
            assertion_verification_results,
        },
        (Ok(()), Err(err)) => PeerAttestationVerdict::AttestationFailed {
            reason: format!("Assertion verification failed: {err:#}"),
            legacy_verification_results,
            assertion_verification_results,
        },
        (Err(err), Ok(())) => PeerAttestationVerdict::AttestationFailed {
            reason: format!("Legacy verification failed: {err:#}"),
            legacy_verification_results,
            assertion_verification_results,
        },
        (Err(legacy_err), Err(assertion_err)) => PeerAttestationVerdict::AttestationFailed {
            reason: format!(
                "Legacy verification failed: {legacy_err:#}. Assertion verification failed: {assertion_err:#}"
            ),
            legacy_verification_results,
            assertion_verification_results,
        },
    }
}

/// Serializes a map of assertions into a deterministic byte vector.
///
/// The serialization format is `id:content|id:content|...`, where `id` is the
/// assertion ID string, encoded as a protobuf message. This is used to create a
/// stable input for the attestation binding token.
fn serialize_assertions(attestations: &BTreeMap<String, Assertion>) -> Vec<u8> {
    attestations
        .iter()
        .map(|(id, assertion)| {
            let mut result = id.encode_to_vec();
            result.push(b':');
            result.extend(assertion.content.clone());
            result.push(b'|');
            result
        })
        .concat()
}
