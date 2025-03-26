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

//! This module provides an implementation of the Attestation Provider, which
//! handles remote attestation between two parties.

use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use core::fmt::Display;

use anyhow::{anyhow, Context, Error, Ok};
use itertools::{EitherOrBoth, Itertools};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, AttestationResults},
    session::v1::{AttestRequest, AttestResponse, EndorsedEvidence},
};

use crate::{config::AttestationProviderConfig, ProtocolEngine};

pub struct AttestationSuccess {
    // Results from individual verifiers keyed by the attestation type ID.
    pub attestation_results: BTreeMap<String, AttestationResults>,
}
#[derive(Debug)]
pub struct AttestationFailure {
    pub reason: String,
    // Per verifier error messages (keyed by the attestation type ID).
    pub error_messages: BTreeMap<String, String>,
}

impl Display for AttestationFailure {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "Attestation failure: {}. Errors from individual verifiers: {}",
            self.reason,
            self.error_messages
                .iter()
                .map(|(id, error)| format!("Verifier ID: {}, error: {}", id, error))
                .collect::<Vec<String>>()
                .join(";")
        )
    }
}

impl From<Error> for AttestationFailure {
    fn from(value: Error) -> Self {
        AttestationFailure { reason: value.to_string(), error_messages: BTreeMap::new() }
    }
}

impl From<AttestationFailure> for Error {
    fn from(value: AttestationFailure) -> Self {
        anyhow!(value.to_string())
    }
}

/// Configuration of the attestation behavior that the AttestationProvider will
/// perform between two parties: Client and Server.
///
/// When configuring the Client: "Self" is the Client and "Peer" is the Server.
/// When configuring the Server: "Self" is the Server and "Peer" is the Client.
#[derive(Clone, Copy)]
pub enum AttestationType {
    /// Both parties attest each other.
    Bidirectional,
    /// "Self" attests itself to the "Peer".
    SelfUnidirectional,
    /// "Peer" attests itself to the "Self".
    PeerUnidirectional,
    /// No attestation.
    Unattested,
}

/// Provider for the particular type of the attestation.
pub trait AttestationProvider: Send {
    // Consume the attestation results when they're ready. Returns None if the
    // attestation still is still pending the incoming peer's data. The result is
    // taken rather than copied since the results returned might be heavy and
    // contain cryptographic material.
    fn take_attestation_result(&mut self)
        -> Option<Result<AttestationSuccess, AttestationFailure>>;
}

/// Aggregates the attestation result from multiple verifiers. Implementations
/// of this trait define the logic of when the overall attestation step succeeds
/// or fails.
pub trait AttestationAggregator: Send {
    fn aggregate_attestation_results(
        &self,
        results: BTreeMap<String, AttestationResults>,
    ) -> Result<AttestationSuccess, AttestationFailure>;
}

pub struct DefaultAttestationAggregator {}

impl AttestationAggregator for DefaultAttestationAggregator {
    fn aggregate_attestation_results(
        &self,
        results: BTreeMap<String, AttestationResults>,
    ) -> Result<AttestationSuccess, AttestationFailure> {
        if results.is_empty() {
            return Err(AttestationFailure {
                reason: "No matching attestation results".to_string(),
                error_messages: BTreeMap::new(),
            });
        };
        let failures: BTreeMap<&String, &AttestationResults> = results
            .iter()
            .filter(|(_, v)| v.status == attestation_results::Status::GenericFailure as i32)
            .collect();
        if !failures.is_empty() {
            return Err(AttestationFailure {
                reason: "Verification failed".to_string(),
                error_messages: failures
                    .iter()
                    .map(|(id, v)| ((*id).clone(), v.reason.clone()))
                    .collect(),
            });
        };
        Ok(AttestationSuccess { attestation_results: results }).map_err(AttestationFailure::from)
    }
}

/// Client-side Attestation Provider that initiates remote attestation with the
/// server.
#[allow(dead_code)]
pub struct ClientAttestationProvider {
    config: AttestationProviderConfig,
    attest_request: Option<AttestRequest>,
    attestation_result: Option<Result<AttestationSuccess, AttestationFailure>>,
}

impl ClientAttestationProvider {
    pub fn create(config: AttestationProviderConfig) -> Result<Self, Error> {
        Ok(Self {
            attest_request: match config.attestation_type {
                AttestationType::Bidirectional | AttestationType::SelfUnidirectional => {
                    Some(AttestRequest {
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
                    })
                }
                AttestationType::PeerUnidirectional => {
                    Some(AttestRequest { endorsed_evidence: BTreeMap::new() })
                }
                AttestationType::Unattested => None,
            },
            config,
            attestation_result: None,
        })
    }
}

impl AttestationProvider for ClientAttestationProvider {
    fn take_attestation_result(
        &mut self,
    ) -> Option<Result<AttestationSuccess, AttestationFailure>> {
        self.attestation_result.take()
    }
}

impl ProtocolEngine<AttestResponse, AttestRequest> for ClientAttestationProvider {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<AttestRequest>> {
        Ok(self.attest_request.take())
    }

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
            AttestationType::SelfUnidirectional => Some(
                Ok(AttestationSuccess { attestation_results: BTreeMap::new() })
                    .map_err(AttestationFailure::from),
            ),
            AttestationType::Unattested => return Err(anyhow!("no attestation message expected'")),
        };
        Ok(Some(()))
    }
}

/// Server-side Attestation Provider that responds to the remote attestation
/// request from the client.
#[allow(dead_code)]
pub struct ServerAttestationProvider {
    config: AttestationProviderConfig,
    attest_response: Option<AttestResponse>,
    attestation_result: Option<Result<AttestationSuccess, AttestationFailure>>,
}

impl ServerAttestationProvider {
    pub fn create(config: AttestationProviderConfig) -> Result<Self, Error> {
        Ok(Self {
            attest_response: match config.attestation_type {
                AttestationType::Bidirectional | AttestationType::SelfUnidirectional => {
                    Some(AttestResponse {
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
                    })
                }
                AttestationType::PeerUnidirectional | AttestationType::Unattested => None,
            },
            config,
            attestation_result: None,
        })
    }
}

impl AttestationProvider for ServerAttestationProvider {
    fn take_attestation_result(
        &mut self,
    ) -> Option<Result<AttestationSuccess, AttestationFailure>> {
        self.attestation_result.take()
    }
}

impl ProtocolEngine<AttestRequest, AttestResponse> for ServerAttestationProvider {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<AttestResponse>> {
        Ok(self.attest_response.take())
    }

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
            AttestationType::SelfUnidirectional => Some(
                Ok(AttestationSuccess { attestation_results: BTreeMap::new() })
                    .map_err(AttestationFailure::from),
            ),
            AttestationType::Unattested => return Err(anyhow!("no attestation message expected'")),
        };
        Ok(Some(()))
    }
}

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
