//
// Copyright 2021 The Project Oak Authors
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

use anyhow::Context;
use openssl::{nid::Nid, x509::X509Extension};
use serde::{Deserialize, Serialize};
use x509_parser::der_parser::{self, oid::Oid};

// Using `NETSCAPE_COMMENT` extension since `rust-openssl` doesn't support custom extensions yet.
// https://github.com/sfackler/rust-openssl/issues/1411
// https://www.alvestrand.no/objectid/2.16.840.1.113730.1.13.html
pub const TEE_EXTENSION_OID: Oid<'static> = der_parser::oid!(2.16.840 .1 .113730 .1 .13);
// TODO(#1867): Add remote attestation support.
const TEST_TEE_MEASUREMENT: &str = "Test TEE measurement";

/// Placeholder implementation of TEE report for remote attestation.
/// https://www.amd.com/system/files/TechDocs/56860.pdf#page=39
///
/// TODO(#1867): Add remote attestation support and use real TEE reports.
#[derive(Deserialize, Serialize, Debug, Default, PartialEq)]
pub struct Report {
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

impl Report {
    /// Placeholder function for collecting TEE measurement of remotely attested TEEs.
    pub fn new(data: &[u8]) -> Self {
        Self {
            measurement: TEST_TEE_MEASUREMENT.to_string().as_bytes().to_vec(),
            data: data.to_vec(),
            ..Default::default()
        }
    }
}

/// Convenience struct for representing X.509 TEE extensions containing TEE reports and TEE
/// provider's certificates.
#[derive(Deserialize, Serialize, Debug, Default, PartialEq)]
pub struct AttestationInfo {
    /// TEE report.
    pub report: Report,
    /// Provider's PEM encoded X.509 certificate that signs TEE firmware keys.
    /// https://tools.ietf.org/html/rfc7468
    pub certificate: Vec<u8>,
}

impl AttestationInfo {
    pub fn from_string(input: &str) -> anyhow::Result<Self> {
        serde_json::from_str(input).context("Couldn't deserialize TEE extension")
    }

    pub fn to_string(&self) -> anyhow::Result<String> {
        serde_json::to_string(&self).context("Couldn't serialize TEE extension")
    }

    /// Serializes [`AttestationInfo`] into a custom [`X509Extension`].
    pub fn to_extension(&self) -> anyhow::Result<X509Extension> {
        let serialized_string = self.to_string()?;
        // [`Nid::NETSCAPE_COMMENT`] is a numerical identifier for an OpenSSL object that
        // corresponds to an X.509 extension implementation.
        X509Extension::new_nid(None, None, Nid::NETSCAPE_COMMENT, &serialized_string)
            .context("Couldn't create X.509 extension")
    }

    /// Verifies that `AttestationInfo::report` is signed by `AttestationInfo::certificate`.
    pub fn verify(&self) -> anyhow::Result<()> {
        // TODO(#1867): Add remote attestation support, use real TEE reports and check that
        // `AttestationInfo::certificate` is signed by one of the root certificates.
        Ok(())
    }
}
