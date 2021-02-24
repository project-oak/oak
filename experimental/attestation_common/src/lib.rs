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

#[cfg(test)]
mod tests;

use anyhow::Context;
use openssl::{nid::Nid, x509::X509Extension};
use serde::{Deserialize, Serialize};
use x509_parser::der_parser::{self, oid::Oid};

// Using `NETSCAPE_COMMENT` extension since `rust-openssl` doesn't support custom
// extensions yet.
// https://github.com/sfackler/rust-openssl/issues/1411
// https://www.alvestrand.no/objectid/2.16.840.1.113730.1.13.html
pub const TEE_EXTENSION_OID: Oid<'static> = der_parser::oid!(2.16.840.1.113730.1.13);

/// Placeholder implementation of TEE report for remote attestation.
#[derive(Deserialize, Serialize, Debug, PartialEq)]
pub struct Report {
    /// TEE measurement, i.e. VM hash.
    pub measurement: Vec<u8>,
    /// Arbitrary data to put into the TEE report.
    pub data: Vec<u8>,
}

impl Report {
    pub fn new(measurement: &[u8], data: &[u8]) -> Self {
        Self {
            measurement: measurement.to_vec(),
            data: data.to_vec(),
        }
    }

    pub fn from_string(input: &str) -> anyhow::Result<Self> {
        serde_json::from_str(input).context("Couldn't deserialize TEE report")
    }

    pub fn to_string(&self) -> anyhow::Result<String> {
        serde_json::to_string(&self).context("Couldn't serialize TEE report")
    }

    /// Return the TEE [`Report`] as a custom [`X509Extension`].
    pub fn to_extension(&self) -> anyhow::Result<X509Extension> {
        let report_string = self.to_string()?;
        // [`Nid::NETSCAPE_COMMENT`] is a numerical identifier for an OpenSSL object that
        // corresponds to an X.509 extension implementation.
        X509Extension::new_nid(None, None, Nid::NETSCAPE_COMMENT, &report_string)
            .context("Couldn't create X.509 extension")
    }
}

/// Computes a SHA-256 digest of `input` and returns it in a form of raw bytes.
pub fn get_sha256(input: &[u8]) -> Vec<u8> {
    use sha2::digest::Digest;
    let mut hasher = sha2::Sha256::new();
    hasher.update(&input);
    hasher.finalize().to_vec()
}
