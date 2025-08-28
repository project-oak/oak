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

use alloc::{string::String, vec::Vec};

use jwt::Token;
use oak_attestation_verification::{decode_event_proto, results::set_session_binding_public_key};
use oak_attestation_verification_types::policy::Policy;
use oak_proto_rust::oak::{
    attestation::v1::{
        ConfidentialSpaceEndorsement, EventAttestationResults, SessionBindingPublicKeyData,
    },
    Variant,
};
use oak_time::Instant;
use sha2::{Digest, Sha256};
use x509_cert::Certificate;

use crate::{
    cosign::{
        self, CosignEndorsement, CosignReferenceValues, CosignVerificationError,
        CosignVerificationReport,
    },
    jwt::{
        verification::{
            report_attestation_token, AttestationTokenVerificationReport,
            AttestationVerificationError,
        },
        Claims, Header,
    },
};

#[derive(Debug)]
pub struct ConfidentialSpaceVerificationReport {
    pub session_binding_public_key: Vec<u8>,
    pub public_key_verification: Result<(), ConfidentialSpaceVerificationError>,
    pub workload_endorsement_verification:
        Option<Result<CosignVerificationReport, CosignVerificationError>>,
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
                workload_endorsement_verification,
                token_report,
            } => {
                if let Some(workload_endorsement_verification) = workload_endorsement_verification {
                    workload_endorsement_verification?.into_checked()?;
                }
                Ok(token_report.into_checked_token().map(|_| session_binding_public_key)?)
            }
            ConfidentialSpaceVerificationReport {
                session_binding_public_key: _,
                public_key_verification: Err(err),
                workload_endorsement_verification: _,
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
    #[error("missing workload endorsement")]
    MissingWorkloadEndorsementError,
    #[error("Sigstore Error: {0}")]
    SigstoreError(#[from] sigstore::error::Error),
    #[error("Failed to parse OCI reference: {0}")]
    ParseError(#[from] oci_spec::distribution::ParseError),
    #[error("Failed to verify Cosign endorsement: {0}")]
    CosignVerificationError(#[from] CosignVerificationError),
}

/// Attstation policy that verifies evidence for a container workload running in
/// Google Cloud Confidential Space.
pub struct ConfidentialSpacePolicy {
    root_certificate: Certificate,
    workload_reference_values: Option<CosignReferenceValues>,
}

impl ConfidentialSpacePolicy {
    /// Creates a new policy with reference values for the platform and the
    /// workload.
    pub fn new(
        root_certificate: Certificate,
        workload_reference_values: CosignReferenceValues,
    ) -> Self {
        Self { root_certificate, workload_reference_values: Some(workload_reference_values) }
    }

    /// Creates a new policy with reference values only for the platform
    /// certificate.
    pub fn new_unendorsed(root_certificate: Certificate) -> Self {
        Self { root_certificate, workload_reference_values: None }
    }

    /// Produce a full report of the provided evidence and endorsement.
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

        let token: Token<Header, Claims, _> = Token::parse_unverified(&endorsement.jwt_token)?;
        let public_key_verification =
            verify_claims_public_key(token.claims(), &public_key_data.session_binding_public_key);

        let image_reference = token.claims().effective_reference()?;
        let workload_endorsement_verification =
            self.workload_reference_values.as_ref().map(|ref_values| {
                match &endorsement.workload_endorsement {
                    Some(workload_endorsement) => Ok(cosign::report_endorsement(
                        CosignEndorsement::from_proto(workload_endorsement)?,
                        &image_reference,
                        ref_values,
                        verification_time,
                    )),
                    None => Err(CosignVerificationError::MissingEndorsement),
                }
            });

        let token_report =
            report_attestation_token(token, &self.root_certificate, &verification_time);

        Ok(ConfidentialSpaceVerificationReport {
            session_binding_public_key: public_key_data.session_binding_public_key.clone(),
            public_key_verification,
            workload_endorsement_verification,
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
        let report = self.report(verification_time, evidence, endorsement)?;
        let mut results = EventAttestationResults { ..Default::default() };
        set_session_binding_public_key(&mut results, &report.into_session_binding_public_key()?);
        Ok(results)
    }
}

fn verify_claims_public_key(
    claims: &Claims,
    expected_public_key: &Vec<u8>,
) -> Result<(), ConfidentialSpaceVerificationError> {
    let public_key_hash = hex::encode(Sha256::digest(expected_public_key));
    if claims.eat_nonce != public_key_hash {
        return Err(ConfidentialSpaceVerificationError::TokenClaimPublicKeyMismatch {
            expected: public_key_hash,
            actual: claims.eat_nonce.clone(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use core::assert_matches::assert_matches;

    use oak_file_utils::{read_testdata, read_testdata_string};
    use oak_proto_rust::oak::attestation::v1::{
        endorsement::Format, Endorsement, Event, Signature, SignedEndorsement,
    };
    use oak_time::make_instant;
    use p256::ecdsa::VerifyingKey;
    use prost::Message;
    use x509_cert::{der::DecodePem, spki::DecodePublicKey};

    use super::*;
    use crate::{
        cosign::{CosignReferenceValues, StatementReport},
        jwt::verification::{CertificateReport, IssuerReport},
    };

    // Note that this is strategically chosen to match (after hashing / base 64
    // encoding) the "eat_nonce" values in testdata claims JSON files (or at
    // least those with valid "eat_nonce" values).
    const BINDING_KEY_BYTES: [u8; 32] = [
        0xad, 0x57, 0x5f, 0x38, 0x17, 0x7e, 0x11, 0x4a, 0x48, 0x2d, 0x5a, 0x24, 0x71, 0x28, 0x73,
        0x64, 0x27, 0x41, 0x53, 0x48, 0x51, 0x5b, 0x76, 0x78, 0x47, 0x11, 0x12, 0x43, 0x01, 0x61,
        0x64, 0x66,
    ];

    #[test]
    fn confidential_space_policy_verify_succeeds() {
        // The time has been set inside the validity interval of the test token and the
        // root certificate.
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let developer_public_key =
            VerifyingKey::from_public_key_pem(&read_testdata_string!("developer_key.pub.pem"))
                .unwrap();
        let event = create_public_key_event(&BINDING_KEY_BYTES);

        let workload_endorsement = Some(SignedEndorsement {
            endorsement: Some(Endorsement {
                format: Format::EndorsementFormatJsonIntoto.into(),
                serialized: read_testdata!("endorsement.json"),
                ..Default::default()
            }),
            // The signature proto has a key ID which we do not use at the moment.
            signature: Some(Signature {
                raw: read_testdata!("endorsement_signature.sig"),
                ..Default::default()
            }),
            ..Default::default()
        });
        let endorsement = ConfidentialSpaceEndorsement {
            jwt_token: read_testdata_string!("valid_token.jwt"),
            workload_endorsement,
        };

        let root_cert = Certificate::from_pem(read_testdata_string!("root_ca_cert.pem")).unwrap();

        let policy = ConfidentialSpacePolicy::new(
            root_cert,
            CosignReferenceValues::partial(developer_public_key),
        );
        let result = policy.verify(current_time, &event.encode_to_vec(), &endorsement.into());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn confidential_space_policy_report_succeeds() {
        // The time has been set inside the validity interval of the test token and the
        // root certificate.
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let developer_public_key =
            VerifyingKey::from_public_key_pem(&read_testdata_string!("developer_key.pub.pem"))
                .unwrap();

        let event = create_public_key_event(&BINDING_KEY_BYTES);

        let workload_endorsement = Some(SignedEndorsement {
            endorsement: Some(Endorsement {
                format: Format::EndorsementFormatJsonIntoto.into(),
                serialized: read_testdata!("endorsement.json"),
                ..Default::default()
            }),
            // The signature proto has a key ID which we do not use at the moment.
            signature: Some(Signature {
                raw: read_testdata!("endorsement_signature.sig"),
                ..Default::default()
            }),
            ..Default::default()
        });
        let endorsement = ConfidentialSpaceEndorsement {
            jwt_token: read_testdata_string!("valid_token.jwt"),
            workload_endorsement,
        };

        let root_cert = Certificate::from_pem(read_testdata_string!("root_ca_cert.pem")).unwrap();

        let policy = ConfidentialSpacePolicy::new(
            root_cert,
            CosignReferenceValues::partial(developer_public_key),
        );
        let result = policy.report(current_time, &event.encode_to_vec(), &endorsement.into());

        assert_matches!(
            result,
            Ok(ConfidentialSpaceVerificationReport {
                ref session_binding_public_key,
                public_key_verification: Ok(()),
                token_report: AttestationTokenVerificationReport {
                    production_image: Ok(()),
                    validity: Ok(()),
                    verification: Ok(_),
                    issuer_report: Ok(CertificateReport {
                        validity: Ok(()),
                        verification: Ok(()),
                        issuer_report: box IssuerReport::OtherCertificate(Ok(CertificateReport {
                            validity: Ok(()),
                            verification: Ok(()),
                            issuer_report: box IssuerReport::Root,
                        })),
                    }),
                },
                workload_endorsement_verification: Some(Ok(CosignVerificationReport {
                statement_verification: Ok(StatementReport{
                    statement_validation: Ok(()),
                    rekor_verification: None
                })
            })),
            }) if *session_binding_public_key == BINDING_KEY_BYTES
        );
    }

    #[test]
    fn confidential_space_policy_report_succeeds_unendorsed() {
        // The time has been set inside the validity interval of the test token and the
        // root certificate.
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let event = create_public_key_event(&BINDING_KEY_BYTES);

        let endorsement = ConfidentialSpaceEndorsement {
            jwt_token: read_testdata_string!("valid_token.jwt"),
            ..Default::default()
        };

        let root_cert = Certificate::from_pem(read_testdata_string!("root_ca_cert.pem")).unwrap();

        let policy = ConfidentialSpacePolicy::new_unendorsed(root_cert);
        let result = policy.report(current_time, &event.encode_to_vec(), &endorsement.into());

        assert_matches!(
            result,
            Ok(ConfidentialSpaceVerificationReport {
                ref session_binding_public_key,
                public_key_verification: Ok(()),
                token_report: AttestationTokenVerificationReport {
                    production_image: Ok(()),
                    validity: Ok(()),
                    verification: Ok(_),
                    issuer_report: Ok(CertificateReport {
                        validity: Ok(()),
                        verification: Ok(()),
                        issuer_report: box IssuerReport::OtherCertificate(Ok(CertificateReport {
                            validity: Ok(()),
                            verification: Ok(()),
                            issuer_report: box IssuerReport::Root,
                        })),
                    }),
                },
                workload_endorsement_verification: None,
            }) if *session_binding_public_key == BINDING_KEY_BYTES
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
