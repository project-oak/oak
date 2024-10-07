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
    boxed::Box,
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};
use core::fmt::Display;

use anyhow::{anyhow, Context, Error, Ok};
use itertools::{EitherOrBoth, Itertools};
#[cfg(test)]
use mockall::automock;
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, AttestationResults, Endorsements, Evidence},
    session::v1::{AttestRequest, AttestResponse, EndorsedEvidence},
};

use crate::{
    config::AttestationProviderConfig, session_binding::SessionBindingVerifier, ProtocolEngine,
};

pub struct AttestationSuccess {
    // Binders allowing to bind different types of attestation to the session (keyed by the
    // attestation type ID).
    pub session_binding_verifiers: BTreeMap<String, Box<dyn SessionBindingVerifier>>,
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

// TODO: b/371139436 - Use definition from `oak_attestation` crate, once DICE
// logic has been moved to a separate crate.
#[cfg_attr(test, automock)]
pub trait Attester: Send {
    fn extend(&mut self, encoded_event: &[u8]) -> anyhow::Result<()>;
    fn quote(&self) -> anyhow::Result<Evidence>;
}

// TODO: b/371139436 - Use definition from `oak_attestation` crate, once DICE
// logic has been moved to a separate crate.
#[cfg_attr(test, automock)]
pub trait Endorser: Send {
    fn endorse<'a>(&self, evidence: Option<&'a Evidence>) -> anyhow::Result<Endorsements>;
}

#[cfg_attr(test, automock)]
// Verifier for the particular type of the attestation.
pub trait AttestationVerifier: Send {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults>;

    fn create_session_binding_verifier(
        &self,
        results: &AttestationResults,
    ) -> anyhow::Result<Box<dyn SessionBindingVerifier>>;
}

/// Configuration of the attestation behavior that the AttestationProvider will
/// perform between two parties: Client and Server.
///
/// When configuring the Client: "Self" is the Client and "Peer" is the Server.
/// When configuring the Server: "Self" is the Server and "Peer" is the Client.
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

// Provider for the particular type of the attestation.
pub trait AttestationProvider: Send {
    // Consume the attestation results when they're ready. Returns None if the
    // attestation still is still pending the incoming peer's data.
    fn take_attestation_result(&mut self)
    -> Option<Result<AttestationSuccess, AttestationFailure>>;
}

// Aggregates the attestation result from multiple verifiers. Implementations of
// this trait define the logic of when the overall attestation step succeeds or
// fails.
pub trait AttestationAggregator: Send {
    fn aggregate_attestation_results(
        &self,
        verifiers: &BTreeMap<String, Box<dyn AttestationVerifier>>,
        results: BTreeMap<String, AttestationResults>,
    ) -> Result<AttestationSuccess, AttestationFailure>;
}

pub struct DefaultAttestationAggregator {}

impl AttestationAggregator for DefaultAttestationAggregator {
    fn aggregate_attestation_results(
        &self,
        verifiers: &BTreeMap<String, Box<dyn AttestationVerifier>>,
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
        Ok(AttestationSuccess {
            session_binding_verifiers: results
                .iter()
                .map(|(id, results)| {
                    Ok((
                        id.clone(),
                        verifiers
                            .get(id)
                            .ok_or(anyhow!(
                                "Missing verifier for attestation result with ID {}",
                                id
                            ))?
                            .create_session_binding_verifier(results)?,
                    ))
                })
                .collect::<Result<BTreeMap<String, Box<dyn SessionBindingVerifier>>, Error>>()?,
        })
        .map_err(AttestationFailure::from)
    }
}

/// Client-side Attestation Provider that initiates remote attestation with the
/// server.
#[allow(dead_code)]
pub struct ClientAttestationProvider {
    config: AttestationProviderConfig,
    attestation_result: Option<Result<AttestationSuccess, AttestationFailure>>,
}

impl ClientAttestationProvider {
    pub fn new(config: AttestationProviderConfig) -> Self {
        Self { config, attestation_result: None }
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
        match self.config.attestation_type {
            AttestationType::Bidirectional | AttestationType::SelfUnidirectional => {
                Ok(Some(AttestRequest {
                    endorsed_evidence: self
                        .config
                        .self_attesters
                        .iter()
                        .map(|(id, attester)| {
                            let evidence = attester.quote()?;
                            // Adds endorsements with corresponding ID.
                            // Endorsements that don't have a corresponding Evidence will not be
                            // added to the `EndorsedEvidence`.
                            let endorsements = self
                                .config
                                .self_endorsers
                                .get(id)
                                .map(|endorser| Ok(endorser.endorse(Some(&evidence))?))
                                .transpose()?;
                            let endorsed_evidence =
                                EndorsedEvidence { evidence: Some(evidence), endorsements };
                            Ok((id.clone(), endorsed_evidence))
                        })
                        .collect::<Result<BTreeMap<String, EndorsedEvidence>, Error>>()?,
                }))
            }
            AttestationType::PeerUnidirectional => {
                Ok(Some(AttestRequest { endorsed_evidence: BTreeMap::new() }))
            }
            AttestationType::Unattested => Ok(None),
        }
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &AttestResponse,
    ) -> anyhow::Result<Option<()>> {
        self.attestation_result = match self.config.attestation_type {
            AttestationType::Bidirectional | AttestationType::PeerUnidirectional => {
                Some(self.config.attestation_aggregator.aggregate_attestation_results(
                    &self.config.peer_verifiers,
                    combine_attestation_results(
                        &self.config.peer_verifiers,
                        &incoming_message.endorsed_evidence,
                    )?,
                ))
            }
            AttestationType::SelfUnidirectional => None,
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
    attestation_result: Option<Result<AttestationSuccess, AttestationFailure>>,
}

impl ServerAttestationProvider {
    pub fn new(config: AttestationProviderConfig) -> Self {
        Self { config, attestation_result: None }
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
        match self.config.attestation_type {
            AttestationType::Bidirectional | AttestationType::SelfUnidirectional => {
                Ok(Some(AttestResponse {
                    endorsed_evidence: self
                        .config
                        .self_attesters
                        .iter()
                        .map(|(id, attester)| {
                            let evidence = attester.quote()?;
                            // Adds endorsements with corresponding ID.
                            // Endorsements that don't have a corresponding Evidence will not be
                            // added to the `EndorsedEvidence`.
                            let endorsements = self
                                .config
                                .self_endorsers
                                .get(id)
                                .map(|endorser| Ok(endorser.endorse(Some(&evidence))?))
                                .transpose()?;
                            let endorsed_evidence =
                                EndorsedEvidence { evidence: Some(evidence), endorsements };
                            Ok((id.clone(), endorsed_evidence))
                        })
                        .collect::<Result<BTreeMap<String, EndorsedEvidence>, Error>>()?,
                }))
            }
            AttestationType::PeerUnidirectional => {
                Ok(Some(AttestResponse { endorsed_evidence: BTreeMap::new() }))
            }
            AttestationType::Unattested => Ok(None),
        }
    }

    fn put_incoming_message(
        &mut self,
        incoming_message: &AttestRequest,
    ) -> anyhow::Result<Option<()>> {
        self.attestation_result = match self.config.attestation_type {
            AttestationType::Bidirectional | AttestationType::PeerUnidirectional => {
                Some(self.config.attestation_aggregator.aggregate_attestation_results(
                    &self.config.peer_verifiers,
                    combine_attestation_results(
                        &self.config.peer_verifiers,
                        &incoming_message.endorsed_evidence,
                    )?,
                ))
            }
            AttestationType::SelfUnidirectional => None,
            AttestationType::Unattested => return Err(anyhow!("no attestation message expected'")),
        };
        Ok(Some(()))
    }
}

fn combine_attestation_results(
    verifiers: &BTreeMap<String, Box<dyn AttestationVerifier>>,
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
