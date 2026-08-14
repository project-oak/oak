//
// Copyright 2025 The Project Oak Authors
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

use alloc::{collections::BTreeMap, str::FromStr};

use jwt::{algorithm::AlgorithmType, header::JoseHeader};
use oak_time::Instant;
use oci_spec::distribution::{ParseError, Reference as OciReference};
use serde::{Deserialize, Serialize};

pub(crate) mod algorithm;
pub mod verification;

/// Partial view of a JWT header with the fields interesting for the validation
/// of the PKI flavour of Confidential Space JWT tokens.
///
/// https://cloud.google.com/confidential-computing/confidential-space/docs/connect-external-resources#attestation_token_structure
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Header {
    /// The algorithm used to sign the JWT.
    ///
    /// https://datatracker.ietf.org/doc/html/rfc7517#section-4.4
    #[serde(rename = "alg")]
    pub algorithm: AlgorithmType,

    /// The x509 chain of the certificate used to sign the JWT.
    ///
    /// https://datatracker.ietf.org/doc/html/rfc7517#section-4.7
    #[serde(rename = "x5c")]
    pub x509_chain: Vec<String>,
}

impl JoseHeader for Header {
    fn algorithm_type(&self) -> AlgorithmType {
        self.algorithm
    }
}

/// The schema for the JWT token claims for Confidential Space.
///
/// https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims
///
/// A number of fields have been omitted: eat_profile, secboot, oemid, hwmodel,
/// swversion
#[derive(Debug, Default, Deserialize, PartialEq, Serialize)]
pub struct Claims {
    /// Audience this token is intended for.
    #[serde(rename = "aud")]
    pub audience: String,
    /// Issuer of the token.
    #[serde(rename = "iss")]
    pub issuer: String,
    /// Subject of the token.
    #[serde(rename = "sub")]
    pub subject: String,
    /// Time at which the token was issued, in seconds since the Unix epoch.
    #[serde(rename = "iat", with = "oak_time::instant::unix_timestamp")]
    pub issued_at: Instant,
    /// Time after which the token is not valid, in seconds since the
    /// Unix epoch.
    #[serde(rename = "exp", with = "oak_time::instant::unix_timestamp")]
    pub not_after: Instant,
    /// Time from which the token is valid, in seconds since the Unix epoch.
    #[serde(rename = "nbf", with = "oak_time::instant::unix_timestamp")]
    pub not_before: Instant,
    /// The debug status for the hardware.
    #[serde(rename = "dbgstat")]
    pub debug_status: String,
    /// Attestation nonce. We only expect one nonce currently.
    pub eat_nonce: String,
    /// Nested claims about sub-modules.
    pub submods: Submods,
    #[serde(rename = "swname")]
    pub software_name: String,
}

impl Claims {
    /// Obtains the effective OCI container [`Reference`] from the
    /// container data by combining the claimed reference (which may be a tag)
    /// with the image digest.
    pub fn effective_reference(&self) -> Result<OciReference, ParseError> {
        let reference = OciReference::from_str(&self.submods.container.image_reference)?;
        Ok(reference.clone_with_digest(self.submods.container.image_digest.clone()))
    }
}

/// Nested claims about sub-modules.
///
/// Some fields have been omitted: confidential_space, gce
#[derive(Debug, Default, Deserialize, PartialEq, Serialize)]
pub struct Submods {
    /// Claims about Confidential Space.
    pub confidential_space: ConfidentialSpaceClaims,
    /// Claims about the container.
    pub container: ContainerClaims,
}

/// Claims about Confidential Space.
///
/// Some fields have been omitted: monitoring_enabled
#[derive(Debug, Default, Deserialize, PartialEq, Serialize)]
pub struct ConfidentialSpaceClaims {
    /// Confidential Space image support attributes:
    /// https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-images#image-lifecycle
    #[serde(default)]
    pub support_attributes: Vec<String>,
}

/// Claims about the container.
#[derive(Debug, Default, Deserialize, PartialEq, Serialize)]
pub struct ContainerClaims {
    /// The container image reference.
    pub image_reference: String,
    /// The container image digest.
    pub image_digest: String,
    /// Environment variables set for the container.
    pub env: BTreeMap<String, String>,
    /// Command line of the container entry point.
    pub args: Vec<String>,
}
