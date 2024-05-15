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

use alloc::vec::Vec;

use oak_proto_rust::oak::{
    attestation::v1::{AttestationResults, Endorsements, Evidence},
    session::v1::{AttestRequest, AttestResponse, EndorsedEvidence},
};

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

#[allow(dead_code)]
struct AttestationProvider<'a> {
    self_attesters: Vec<&'a dyn Attester>,
    peer_verifiers: Vec<&'a dyn AttestationVerifier>,
}

impl<'a> AttestationProvider<'a> {
    pub fn new(
        self_attesters: Vec<&'a dyn Attester>,
        peer_verifiers: Vec<&'a dyn AttestationVerifier>,
    ) -> Self {
        Self { self_attesters, peer_verifiers }
    }
}

/// Client-side Attestation Provider that initiates remote attestation with the
/// server.
#[allow(dead_code)]
pub struct ClientAttestationProvider<'a> {
    inner: AttestationProvider<'a>,
}

impl<'a> ClientAttestationProvider<'a> {
    pub fn new(
        self_attesters: Vec<&'a dyn Attester>,
        peer_verifiers: Vec<&'a dyn AttestationVerifier>,
    ) -> Self {
        Self { inner: AttestationProvider::new(self_attesters, peer_verifiers) }
    }

    pub fn get_request(&self) -> anyhow::Result<AttestRequest> {
        core::unimplemented!();
    }

    pub fn put_response(&self, _response: &AttestResponse) -> anyhow::Result<()> {
        core::unimplemented!();
    }

    pub fn get_attestation_results(self) -> Option<AttestationResults> {
        core::unimplemented!();
    }
}

/// Server-side Attestation Provider that responds to the remote attestation
/// request from the client.
#[allow(dead_code)]
pub struct ServerAttestationProvider<'a> {
    inner: AttestationProvider<'a>,
}

impl<'a> ServerAttestationProvider<'a> {
    pub fn new(
        self_attesters: Vec<&'a dyn Attester>,
        peer_verifiers: Vec<&'a dyn AttestationVerifier>,
    ) -> Self {
        Self { inner: AttestationProvider::new(self_attesters, peer_verifiers) }
    }

    pub fn put_request(&self, _request: &AttestRequest) -> anyhow::Result<()> {
        core::unimplemented!();
    }

    pub fn get_response(&self) -> anyhow::Result<AttestResponse> {
        core::unimplemented!();
    }

    pub fn get_attestation_results(self) -> Option<AttestationResults> {
        core::unimplemented!();
    }
}
