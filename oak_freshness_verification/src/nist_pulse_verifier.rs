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

use alloc::{boxed::Box, format, string::String};
use core::error::Error;

use anyhow::Context;
use hex::FromHexError;
#[cfg(test)]
use mockall::automock;
use oak_proto_rust::oak::crypto::v1::ProofOfFreshness;
use serde::{Deserialize, Serialize};
use x509_cert::{Certificate, der::DecodePem};

const NIST_WEB_PREFIX: &str = "https://beacon.nist.gov";
// TODO: b/424736845 - Add support for version 2.1
const NIST_VERSION: &str = "2.0";

#[derive(thiserror::Error, Debug)]
pub enum ProofOfFreshnessVerificationError {
    #[error("OutputValue not found; expected: {expected}, actual: {actual}")]
    OutputValueNotFound { expected: String, actual: String },
    #[error("Invalid hexadecimal: {0}")]
    InvalidHexadecimal(#[from] FromHexError),
    #[error("API call failed: {0}")]
    ApiCallFailed(#[from] Box<dyn Error>),
    #[error("JSON parsing failed: {0}")]
    JsonParsingFailed(#[from] serde_json::Error),
    // Utilize the error string since x509_cert::der::Error requires StdErr support and x509_cert
    // in Oak is used for no-std crates.
    #[error("Unable to parse certificate: {err}")]
    CertificateParsingFailed { err: String },
    #[error("Signature verification not implemented")]
    SignatureVerificationNotImplemented,
}

/// Represents a single value within the `listValues` array.
#[derive(Debug, Serialize, Deserialize)]
pub struct ListValue {
    pub uri: String,
    #[serde(rename = "type")] // Use rename since "type" is a Rust keyword
    pub value_type: String,
    pub value: String,
}

/// Represents the `external` object within the `pulse` data.
#[derive(Debug, Serialize, Deserialize)]
pub struct External {
    #[serde(rename = "sourceId")]
    pub source_id: String,
    #[serde(rename = "statusCode")]
    pub status_code: i64,
    pub value: String,
}

/// Represents the main `pulse` object.
#[derive(Debug, Serialize, Deserialize)]
pub struct Pulse {
    pub uri: String,
    pub version: String,
    #[serde(rename = "cipherSuite")]
    pub cipher_suite: i64,
    pub period: i64,
    #[serde(rename = "certificateId")]
    pub certificate_id: String,
    #[serde(rename = "chainIndex")]
    pub chain_index: i64,
    #[serde(rename = "pulseIndex")]
    pub pulse_index: i64,
    #[serde(rename = "timeStamp")]
    pub time_stamp: String,
    #[serde(rename = "localRandomValue")]
    pub local_random_value: String,
    pub external: External,
    #[serde(rename = "listValues")]
    pub list_values: Vec<ListValue>,
    #[serde(rename = "precommitmentValue")]
    pub precommitment_value: String,
    #[serde(rename = "statusCode")]
    pub status_code: i64,
    #[serde(rename = "signatureValue")]
    pub signature_value: String,
    #[serde(rename = "outputValue")]
    pub output_value: String,
}

#[derive(Deserialize, Serialize, Debug)]
struct PulseResponse {
    pulse: Pulse,
}

// Simple API get request trait that can be mocked in tests.
#[cfg_attr(test, automock)]
pub trait ApiGetter {
    fn get(&self, url: &str) -> Result<String, Box<dyn Error>>;
}

// Fetches the contents of a URL using the `ureq` crate.
pub struct UreqGetter {}

impl ApiGetter for UreqGetter {
    fn get(&self, url: &str) -> Result<String, Box<dyn Error>> {
        let res: ureq::Response =
            ureq::get(url).call().with_context(|| format!("fetching URL {url}"))?;
        let body_string =
            res.into_string().with_context(|| format!("reading response body from URL {url}"))?;
        Ok(body_string)
    }
}

// Formats the expected nist pulse URI from the ProofOfFreshness proto.
fn create_nist_pulse_uri(proof_of_freshness: &ProofOfFreshness) -> String {
    format!(
        "{}/beacon/{}/chain/{}/pulse/{}",
        NIST_WEB_PREFIX,
        NIST_VERSION,
        proof_of_freshness.nist_chain_index,
        proof_of_freshness.nist_pulse_index
    )
}

// Formats the expected nist beacon certificate URI from the ProofOfFreshness
// proto.
fn create_nist_beacon_certificate_uri(certificate_id: &String) -> String {
    format!("{NIST_WEB_PREFIX}/beacon/{NIST_VERSION}/certificate/{certificate_id}")
}

// Ensures that the ProofOfFreshness output value is equal to the passed in
// output_value.
fn verify_output_value(
    proof_of_freshness: &ProofOfFreshness,
    output_value: &str,
) -> Result<(), ProofOfFreshnessVerificationError> {
    let output_value_bytes: Vec<u8> = hex::decode(output_value)?;
    match output_value_bytes == proof_of_freshness.nist_pulse_output_value {
        true => Ok(()),
        false => Err(ProofOfFreshnessVerificationError::OutputValueNotFound {
            expected: hex::encode(proof_of_freshness.nist_pulse_output_value.clone())
                .to_ascii_uppercase(),
            actual: output_value.to_string().to_ascii_uppercase(),
        }),
    }
}

// Verifies that a ProofOfFreshness entry is based on NIST's Interoperable
// Randomness Beacon project: https://csrc.nist.gov/projects/interoperable-randomness-beacons/beacon-20.
pub struct NistPulseVerifier {
    data_fetcher: Box<dyn ApiGetter>,
}

impl NistPulseVerifier {
    pub fn new(data_fetcher: Box<dyn ApiGetter>) -> Self {
        Self { data_fetcher }
    }

    // TODO: b/424736845 - Verify signature of pulse and CA certificate.
    pub fn verify(
        &self,
        proof_of_freshness: ProofOfFreshness,
    ) -> Result<(), ProofOfFreshnessVerificationError> {
        let nist_pulse_uri = create_nist_pulse_uri(&proof_of_freshness);

        let pulse_str = self.data_fetcher.get(&nist_pulse_uri)?;
        let pulse_response: PulseResponse = serde_json::from_str(&pulse_str)?;

        verify_output_value(&proof_of_freshness, &pulse_response.pulse.output_value)?;

        // TODO: b/424736845 - Inject certificate code into the NistPulseVerifier type
        // so the crate can be agnostic to how certificate is fetched.
        let nist_beacon_certificate_uri =
            create_nist_beacon_certificate_uri(&pulse_response.pulse.certificate_id);
        let certificate_str = self.data_fetcher.get(&nist_beacon_certificate_uri)?;
        let _certificate = Certificate::from_pem(certificate_str.as_bytes()).map_err(|e| {
            ProofOfFreshnessVerificationError::CertificateParsingFailed { err: e.to_string() }
        })?;

        Err(ProofOfFreshnessVerificationError::SignatureVerificationNotImplemented)
    }
}
