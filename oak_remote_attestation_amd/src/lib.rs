//
// Copyright 2022 The Project Oak Authors
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

//! This crate implements remote attestation primitives from `oak_remote_attestation_interactive`
//! based on AMD-SEV-SNP.
//!
//! Currently only contains some placeholder structs, which will be replaced with actual
//! functionality as part of #2842.

#![no_std]

extern crate alloc;

use alloc::{
    string::{String, ToString},
    vec::Vec,
};
use anyhow::Context;
use oak_remote_attestation_noninteractive::{
    AttestationEvidence, AttestationVerifier, Attester, ReferenceValue,
};
use serde::{Deserialize, Serialize};

// TODO(#2842): Add remote attestation support.
#[derive(Clone)]
pub struct PlaceholderAmdAttester;

impl Attester for PlaceholderAmdAttester {
    fn generate_attestation_evidence(
        &self,
        attested_data: &[u8],
    ) -> anyhow::Result<AttestationEvidence> {
        let attestation_report = PlaceholderAmdReport::new(attested_data)
            .to_string()
            .map(|s| s.as_bytes().to_vec())
            .context("couldn't generate attestation report")?;
        Ok(AttestationEvidence { attestation_report })
    }
}

// TODO(#2842): Add remote attestation support.
#[derive(Clone)]
pub struct PlaceholderAmdAttestationVerifier;

impl AttestationVerifier for PlaceholderAmdAttestationVerifier {
    fn verify_attestation(
        &self,
        evidence: &AttestationEvidence,
        reference_value: &ReferenceValue,
    ) -> anyhow::Result<()> {
        let attestation_report = PlaceholderAmdReport::from_string(
            core::str::from_utf8(&evidence.attestation_report)
                .map_err(|_err| anyhow::anyhow!("couldn't parse remote attestation report"))?,
        )?;
        let actual_attested_data = attestation_report.data;
        if actual_attested_data == reference_value.attested_data {
            Ok(())
        } else {
            Err(anyhow::anyhow!(
                "invalid attested data; got: {:?}, expected: {:?}",
                actual_attested_data,
                reference_value.attested_data
            ))
        }
    }
}

/// Placeholder implementation of TEE report for remote attestation.
///
/// <https://www.amd.com/system/files/TechDocs/56860.pdf#page=39>
// TODO(#2842): Add remote attestation support.
#[derive(Deserialize, Serialize, Debug, Default, PartialEq)]
pub struct PlaceholderAmdReport {
    /// Version number of this attestation report.
    pub version: u8,
    /// Security version number of SNP firmware.
    pub svn: u8,
    /// The installed version of firmware.
    pub platform_version: u8,
    /// Arbitrary data to put into the TEE report.
    pub data: Vec<u8>,
    /// TEE measurement, i.e. VM hash.
    pub measurement: Vec<u8>,
    /// Signature of this report.
    pub signature: Vec<u8>,
}

// TODO(#2842): Add remote attestation support.
const TEST_TEE_MEASUREMENT: &str = "Test TEE measurement";

impl PlaceholderAmdReport {
    /// Placeholder function for collecting TEE measurement of remotely attested TEEs.
    pub fn new(data: &[u8]) -> Self {
        Self {
            measurement: TEST_TEE_MEASUREMENT.to_string().as_bytes().to_vec(),
            data: data.to_vec(),
            ..Default::default()
        }
    }
}

impl PlaceholderAmdReport {
    // TODO(#2842): Use raw report instead of JSON.
    pub fn from_string(input: &str) -> anyhow::Result<Self> {
        serde_json::from_str(input)
            .map_err(|_err| anyhow::anyhow!("couldn't deserialize attestation report"))
    }

    // TODO(#2842): Use raw report instead of JSON.
    pub fn to_string(&self) -> anyhow::Result<String> {
        serde_json::to_string(&self)
            .map_err(|_err| anyhow::anyhow!("couldn't serialize attestation report"))
    }
}
