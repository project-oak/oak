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

use alloc::{boxed::Box, collections::BTreeMap, string::String};

use anyhow::{anyhow, Context, Error, Ok};
use itertools::{EitherOrBoth, Itertools};
#[cfg(test)]
use mockall::automock;
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, AttestationResults, Endorsements, Evidence},
    session::v1::{AttestRequest, AttestResponse, EndorsedEvidence},
};

use crate::{config::AttestationProviderConfig, ProtocolEngine};

#[cfg_attr(test, automock)]
pub trait Attester {
    fn get_endorsed_evidence(&self) -> anyhow::Result<EndorsedEvidence>;
}

#[cfg_attr(test, automock)]
pub trait AttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults>;
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

pub trait AttestationProvider {
    fn take_attestation_report(&mut self) -> Option<AttestationResults>;
}

pub trait AttestationAggregator {
    fn aggregate_attestation_results(
        &self,
        results: BTreeMap<String, AttestationResults>,
    ) -> Result<AttestationResults, Error>;
}

pub struct DefaultAttestationAggregator {}

impl AttestationAggregator for DefaultAttestationAggregator {
    fn aggregate_attestation_results(
        &self,
        results: BTreeMap<String, AttestationResults>,
    ) -> Result<AttestationResults, Error> {
        if results.is_empty() {
            return Ok(AttestationResults {
                status: attestation_results::Status::GenericFailure.into(),
                reason: String::from("No matching attestation results"),
                ..Default::default()
            });
        };
        let failures: BTreeMap<&String, &AttestationResults> = results
            .iter()
            .filter(|(_, v)| v.status == attestation_results::Status::GenericFailure.into())
            .collect();
        if !failures.is_empty() {
            return Ok(AttestationResults {
                status: attestation_results::Status::GenericFailure.into(),
                reason: failures
                    .iter()
                    .map(|(id, v)| format!("Id: {}, error: {}; ", id, v.reason))
                    .collect(),
                ..Default::default()
            });
        };
        // In case of multiple success matches we just return the first one.
        // Using unwrap(), as we have already checked that results are not empty.
        Ok(results.first_key_value().unwrap().1.clone())
    }
}

/// Client-side Attestation Provider that initiates remote attestation with the
/// server.
#[allow(dead_code)]
pub struct ClientAttestationProvider {
    config: AttestationProviderConfig,
    attestation_results: Option<AttestationResults>,
}

impl ClientAttestationProvider {
    pub fn new(config: AttestationProviderConfig) -> Self {
        Self { config, attestation_results: None }
    }
}

impl AttestationProvider for ClientAttestationProvider {
    fn take_attestation_report(&mut self) -> Option<AttestationResults> {
        self.attestation_results.take()
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
                        .map(|(id, att)| Ok((id.clone(), att.get_endorsed_evidence()?)))
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
        self.attestation_results = match self.config.attestation_type {
            AttestationType::Bidirectional | AttestationType::PeerUnidirectional => {
                Some(self.config.attestation_aggregator.aggregate_attestation_results(
                    combine_attestation_results(
                        &self.config.peer_verifiers,
                        &incoming_message.endorsed_evidence,
                    )?,
                )?)
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
    attestation_results: Option<AttestationResults>,
}

impl ServerAttestationProvider {
    pub fn new(config: AttestationProviderConfig) -> Self {
        Self { config, attestation_results: None }
    }
}

impl AttestationProvider for ServerAttestationProvider {
    fn take_attestation_report(&mut self) -> Option<AttestationResults> {
        self.attestation_results.take()
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
                        .map(|(id, att)| Ok((id.clone(), att.get_endorsed_evidence()?)))
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
        self.attestation_results = match self.config.attestation_type {
            AttestationType::Bidirectional | AttestationType::PeerUnidirectional => {
                Some(self.config.attestation_aggregator.aggregate_attestation_results(
                    combine_attestation_results(
                        &self.config.peer_verifiers,
                        &incoming_message.endorsed_evidence,
                    )?,
                )?)
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
