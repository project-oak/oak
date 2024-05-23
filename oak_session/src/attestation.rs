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

use oak_proto_rust::oak::{
    attestation::v1::{AttestationResults, Endorsements, Evidence},
    session::v1::{AttestRequest, AttestResponse, EndorsedEvidence},
};

use crate::{config::AttestationProviderConfig, ProtocolEngine};

pub trait Attester {
    fn get_endorsed_evidence(&self) -> anyhow::Result<EndorsedEvidence>;
}

pub trait AttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults>;
}

/// Configuration of the attestation behavior that the AttestationProtiver will
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
}

pub trait AttestationProvider {
    fn get_attestation_results(self) -> Option<AttestationResults>;
}

/// Client-side Attestation Provider that initiates remote attestation with the
/// server.
#[allow(dead_code)]
pub struct ClientAttestationProvider<'a> {
    config: AttestationProviderConfig<'a>,
}

impl<'a> ClientAttestationProvider<'a> {
    pub fn new(config: AttestationProviderConfig<'a>) -> Self {
        Self { config }
    }
}

impl<'a> AttestationProvider for ClientAttestationProvider<'a> {
    fn get_attestation_results(self) -> Option<AttestationResults> {
        core::unimplemented!();
    }
}

impl<'a> ProtocolEngine<AttestResponse, AttestRequest> for ClientAttestationProvider<'a> {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<AttestRequest>> {
        core::unimplemented!();
    }

    fn put_incoming_message(
        &mut self,
        _incoming_message: &AttestResponse,
    ) -> anyhow::Result<Option<()>> {
        core::unimplemented!();
    }
}

/// Server-side Attestation Provider that responds to the remote attestation
/// request from the client.
#[allow(dead_code)]
pub struct ServerAttestationProvider<'a> {
    config: AttestationProviderConfig<'a>,
}

impl<'a> ServerAttestationProvider<'a> {
    pub fn new(config: AttestationProviderConfig<'a>) -> Self {
        Self { config }
    }
}

impl<'a> AttestationProvider for ServerAttestationProvider<'a> {
    fn get_attestation_results(self) -> Option<AttestationResults> {
        core::unimplemented!();
    }
}

impl<'a> ProtocolEngine<AttestRequest, AttestResponse> for ServerAttestationProvider<'a> {
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<AttestResponse>> {
        core::unimplemented!();
    }

    fn put_incoming_message(
        &mut self,
        _incoming_message: &AttestRequest,
    ) -> anyhow::Result<Option<()>> {
        core::unimplemented!();
    }
}
