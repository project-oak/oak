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

//! This crate implements remote attestation primitives from `oak_remote_attestation` based on
//! AMD-SEV-SNP.
//!
//! Currently only contains some placeholder structs, which will be replaced with actual
//! functionality as part of #1867.

#![no_std]

extern crate alloc;

use alloc::{
    string::{String, ToString},
    vec::Vec,
};
use oak_remote_attestation::handshaker::{AttestationGenerator, AttestationVerifier};
use serde::{Deserialize, Serialize};

// TODO(#1867): Add remote attestation support and use real TEE reports.
#[derive(Clone)]
pub struct PlaceholderAmdAttestationGenerator;

impl AttestationGenerator for PlaceholderAmdAttestationGenerator {
    fn generate_attestation(&self, attested_data: &[u8]) -> anyhow::Result<Vec<u8>> {
        PlaceholderAmdReport::new(attested_data)
            .to_string()
            .map(|s| s.as_bytes().to_vec())
    }
}

// TODO(#1867): Add remote attestation support and use real TEE reports.
#[derive(Clone)]
pub struct PlaceholderAmdAttestationVerifier;

impl AttestationVerifier for PlaceholderAmdAttestationVerifier {
    fn verify_attestation(
        &self,
        attestation: &[u8],
        expected_attested_data: &[u8],
    ) -> anyhow::Result<()> {
        let attestation_report = PlaceholderAmdReport::from_string(
            core::str::from_utf8(attestation)
                .map_err(|_err| anyhow::anyhow!("could not parse remote attestation report"))?,
        )?;
        let actual_attested_data = attestation_report.data;
        if actual_attested_data == expected_attested_data {
            Ok(())
        } else {
            Err(anyhow::anyhow!(
                "invalid attested data; got: {:?}, expected: {:?}",
                actual_attested_data,
                expected_attested_data
            ))
        }
    }
}

/// Placeholder implementation of TEE report for remote attestation.
///
/// <https://www.amd.com/system/files/TechDocs/56860.pdf#page=39>
///
/// TODO(#1867): Add remote attestation support and use real TEE reports.
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

// TODO(#1867): Add remote attestation support.
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
    pub fn from_string(input: &str) -> anyhow::Result<Self> {
        serde_json::from_str(input)
            .map_err(|_err| anyhow::anyhow!("Couldn't deserialize attestation report"))
    }

    pub fn to_string(&self) -> anyhow::Result<String> {
        serde_json::to_string(&self)
            .map_err(|_err| anyhow::anyhow!("Couldn't serialize attestation report"))
    }
}
