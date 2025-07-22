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

use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
};

use jwt::Token;
use oak_attestation_verification::{decode_event_proto, policy::SESSION_BINDING_PUBLIC_KEY_ID};
use oak_attestation_verification_types::policy::Policy;
use oak_proto_rust::oak::{
    attestation::v1::{
        ConfidentialSpaceEndorsement, EventAttestationResults, SessionBindingPublicKeyData,
    },
    Variant,
};
use oak_time::Instant;
use serde::Deserialize;
use serde_json::Value;
use sha2::Digest;
use x509_cert::Certificate;

use crate::verification::{
    report_attestation_token, AttestationTokenVerificationReport, AttestationVerificationError,
};

#[derive(Debug)]
pub struct ConfidentialSpaceVerificationReport {
    session_binding_public_key: Vec<u8>,
    pub public_key_verification: Result<(), ConfidentialSpaceVerificationError>,
    pub token_report: AttestationTokenVerificationReport,
}

impl ConfidentialSpaceVerificationReport {
    pub fn into_session_binding_public_key(
        self,
    ) -> Result<Vec<u8>, ConfidentialSpaceVerificationError> {
        match self {
            ConfidentialSpaceVerificationReport {
                session_binding_public_key,
                public_key_verification: Ok(()),
                token_report,
            } => Ok(token_report.into_checked_token().map(|_| session_binding_public_key)?),
            ConfidentialSpaceVerificationReport {
                session_binding_public_key: _,
                public_key_verification: Err(err),
                token_report: _,
            } => Err(err),
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum ConfidentialSpaceVerificationError {
    #[error("Missing field: {0}")]
    MissingField(&'static str),
    #[error("Failed to decode proto: {0}")]
    ProtoDecodeError(#[from] anyhow::Error),
    #[error("Failed to decode Variant: {0}")]
    VariantDecodeError(&'static str),
    #[error("Failed to parse Token: {0}")]
    TokenParseError(#[from] jwt::error::Error),
    #[error("Token public key mismatch; expected {expected} but got {actual}")]
    TokenClaimPublicKeyMismatch { expected: String, actual: String },
    #[error("Failed to deserialize nonce: {0}")]
    NonceDeserializeError(#[from] serde_json::error::Error),
    #[error("Failed to verify Token: {0}")]
    TokenVerificationError(#[from] AttestationVerificationError),
}

// Private claim field in Confidential Space attestation tokens with
// the attestation nonce.
// https://cloud.google.com/confidential-computing/confidential-space/docs/connect-external-resources#attestation_token_structure
const EAT_NONCE: &str = "eat_nonce";

pub struct ConfidentialSpacePolicy {
    root_certificate: Certificate,
}

impl ConfidentialSpacePolicy {
    pub fn new(root_certificate: Certificate) -> Self {
        Self { root_certificate }
    }

    pub fn report(
        &self,
        verification_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> Result<ConfidentialSpaceVerificationReport, ConfidentialSpaceVerificationError> {
        let public_key_data = decode_event_proto::<SessionBindingPublicKeyData>(
            "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData",
            evidence,
        )?;

        let endorsement: ConfidentialSpaceEndorsement = endorsement
            .try_into()
            .map_err(ConfidentialSpaceVerificationError::VariantDecodeError)?;

        let token = Token::parse_unverified(&endorsement.jwt_token)?;
        let public_key_verification =
            verify_claims_public_key(token.claims(), &public_key_data.session_binding_public_key);
        let token_report =
            report_attestation_token(token, &self.root_certificate, &verification_time);

        // TODO: b/426463266 - Verify claims about the platform/container

        Ok(ConfidentialSpaceVerificationReport {
            session_binding_public_key: public_key_data.session_binding_public_key.clone(),
            public_key_verification,
            token_report,
        })
    }
}

// We have to use [`Policy<[u8]>`] instead of [`EventPolicy`], because
// Rust doesn't yet support implementing trait aliases.
// <https://github.com/rust-lang/rfcs/blob/master/text/1733-trait-alias.md>
impl Policy<[u8]> for ConfidentialSpacePolicy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        Ok(EventAttestationResults {
            artifacts: BTreeMap::from([(
                SESSION_BINDING_PUBLIC_KEY_ID.to_string(),
                self.report(verification_time, evidence, endorsement)?
                    .into_session_binding_public_key()?,
            )]),
        })
    }
}

fn verify_claims_public_key(
    claims: &Value,
    expected_public_key: &Vec<u8>,
) -> Result<(), ConfidentialSpaceVerificationError> {
    let public_key_hash = hex::encode(sha2::Sha256::digest(expected_public_key));
    // We expect only one nonce, therefore a scalar string rather than an array.
    let eat_nonce = String::deserialize(&claims[EAT_NONCE])?;
    if eat_nonce != public_key_hash {
        return Err(ConfidentialSpaceVerificationError::TokenClaimPublicKeyMismatch {
            expected: public_key_hash,
            actual: eat_nonce,
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use core::assert_matches::assert_matches;

    use oak_proto_rust::oak::attestation::v1::Event;
    use oak_time::make_instant;
    use prost::Message;
    use x509_cert::{
        der::{self, DecodePem},
        spki::DecodePublicKey,
    };

    use super::*;
    use crate::verification::{CertificateReport, IssuerReport};

    #[test]
    fn confidential_space_policy_verify_succeeds() {
        // The time has been set inside the validity interval of the test token and the
        // root certificate.
        const TOKEN: &str = include_str!("../testdata/confidential_space_valid.jwt");
        const PUBLIC_KEY: &str = include_str!("../testdata/confidential_space_public_key.pem");
        const CONFIDENTIAL_SPACE_ROOT_CERT_PEM: &str =
            include_str!("../testdata/confidential_space_root.pem");
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let public_key = der::Document::from_public_key_pem(PUBLIC_KEY).unwrap().to_vec();
        let event = create_public_key_event(&public_key);

        let endorsement =
            ConfidentialSpaceEndorsement { jwt_token: TOKEN.to_owned(), ..Default::default() };

        let root_cert = Certificate::from_pem(CONFIDENTIAL_SPACE_ROOT_CERT_PEM).unwrap();

        let policy = ConfidentialSpacePolicy::new(root_cert);
        let result = policy.verify(current_time, &event.encode_to_vec(), &endorsement.into());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn confidential_space_policy_report_succeeds() {
        // The time has been set inside the validity interval of the test token and the
        // root certificate.
        const TOKEN: &str = include_str!("../testdata/confidential_space_valid.jwt");
        const PUBLIC_KEY: &str = include_str!("../testdata/confidential_space_public_key.pem");
        const CONFIDENTIAL_SPACE_ROOT_CERT_PEM: &str =
            include_str!("../testdata/confidential_space_root.pem");
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let public_key = der::Document::from_public_key_pem(PUBLIC_KEY).unwrap().to_vec();
        let event = create_public_key_event(&public_key);

        let endorsement =
            ConfidentialSpaceEndorsement { jwt_token: TOKEN.to_owned(), ..Default::default() };

        let root_cert = Certificate::from_pem(CONFIDENTIAL_SPACE_ROOT_CERT_PEM).unwrap();

        let policy = ConfidentialSpacePolicy::new(root_cert);
        let result = policy.report(current_time, &event.encode_to_vec(), &endorsement.into());

        assert_matches!(
            result,
            Ok(ConfidentialSpaceVerificationReport {
                ref session_binding_public_key,
                public_key_verification: Ok(()),
                token_report: AttestationTokenVerificationReport{
                    validity: Ok(()),
                    verification: Ok(_),
                    issuer_report: Ok(CertificateReport {
                        validity: Ok(()),
                        verification: Ok(()),
                        issuer_report: box IssuerReport::OtherCertificate(
                            Ok(CertificateReport {
                                validity: Ok(()),
                                verification: Ok(()),
                                issuer_report: box IssuerReport::SelfSigned,
                            })
                        ),
                    })
                }
            }) if *session_binding_public_key == public_key,
        );
    }

    fn create_public_key_event(session_binding_public_key: &[u8]) -> Event {
        Event {
            tag: "session_binding_key".to_string(),
            event: Some(prost_types::Any {
                type_url: "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData"
                    .to_string(),
                value: SessionBindingPublicKeyData {
                    session_binding_public_key: session_binding_public_key.to_vec(),
                }
                .encode_to_vec(),
            }),
        }
    }
}
