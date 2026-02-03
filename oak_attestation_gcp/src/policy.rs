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
use oak_digest::Digest;
use oak_proto_rust::oak::{
    Variant,
    attestation::v1::{
        BinaryReferenceValue, ConfidentialSpaceEndorsement, EventAttestationResults,
        SessionBindingPublicKeyData, SignedEndorsement, binary_reference_value,
    },
};
use oak_time::Instant;
use oci_spec::distribution::Reference as OciReference;
use sha2::{Digest as OtherDigest, Sha256};
use verify_endorsement::verify_endorsement;
use x509_cert::Certificate;

use crate::{
    OAK_SESSION_NOISE_V1_AUDIENCE,
    jwt::{
        Claims, Header,
        verification::{
            AttestationTokenVerificationReport, AttestationVerificationError,
            report_attestation_token,
        },
    },
};

#[derive(Debug)]
pub struct ConfidentialSpaceVerificationReport {
    pub session_binding_public_key: Vec<u8>,
    pub public_key_verification: Result<(), ConfidentialSpaceVerificationError>,
    pub workload_endorsement_verification: Option<Result<(), ConfidentialSpaceVerificationError>>,
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
                    workload_endorsement_verification?;
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
    #[error("Invalid field: {0}")]
    InvalidField(&'static str),
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
    #[error("Failed to parse OCI reference: {0}")]
    ParseError(#[from] oci_spec::distribution::ParseError),
    #[error("Failed to verify endorsement: {0}")]
    EndorsementVerificationError(String),
    #[error("Failed to verify container image reference; {actual} is not prefixed by {prefix}")]
    EndorsementContainerImageVerifyError { actual: String, prefix: String },
}

pub(crate) fn verify_endorsement_wrapper(
    verification_time: Instant,
    image_reference: &OciReference,
    signed_endorsement: &SignedEndorsement,
    ref_value: &BinaryReferenceValue,
) -> Result<(), ConfidentialSpaceVerificationError> {
    use ConfidentialSpaceVerificationError::{
        EndorsementVerificationError as EVError, InvalidField as IFError,
    };

    let typed_hash = image_reference.digest().ok_or(
        ConfidentialSpaceVerificationError::MissingField("Missing digest in OCI reference"),
    )?;
    let digest = Digest::from_typed_hash(typed_hash)
        .map_err(|_| IFError("Malformed digest in OCI reference"))?;

    match ref_value.r#type.as_ref() {
        Some(binary_reference_value::Type::Endorsement(val)) => {
            let statement =
                verify_endorsement(verification_time.into_unix_millis(), signed_endorsement, val)
                    .map_err(|err| EVError(format!("{err:#}")))?;
            statement
                .validate_subject(&digest.clone().into())
                .map_err(|err| EVError(format!("{err:#}")))
        }
        Some(binary_reference_value::Type::Skip(_)) => Ok(()),
        Some(binary_reference_value::Type::Digests(digests)) => {
            // We expect the digest to be SHA2-256.
            if let Digest::Sha256(h) = digest {
                if digests.digests.iter().any(|d| d.sha2_256 == h.as_ref()) {
                    Ok(())
                } else {
                    Err(EVError("Digest mismatch".to_string()))
                }
            } else {
                Err(IFError("Missing SHA2-256 digest in OCI reference"))
            }
        }
        None => Err(IFError("Missing reference value type")),
    }
}

// Workload reference values can either be `EndorsementReferenceValue` protos or
// a string pointing to the referenced container image.
pub enum WorkloadReferenceValues {
    ImageReferenceValue(BinaryReferenceValue),
    // See https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims#workload-container-claims
    // TODO: b/439861326 - Remove this field once endorsements are supported with Oak Transparent
    // release.
    ContainerImageReferencePrefix(String),
}

/// Attstation policy that verifies evidence for a container workload running in
/// Google Cloud Confidential Space.
pub struct ConfidentialSpacePolicy {
    root_certificate: Certificate,
    workload_reference_values: Option<WorkloadReferenceValues>,
}

impl ConfidentialSpacePolicy {
    /// Creates a new policy with reference values for the platform and the
    /// workload.
    pub(crate) fn new(
        root_certificate: Certificate,
        workload_reference_values: WorkloadReferenceValues,
    ) -> Self {
        Self { root_certificate, workload_reference_values: Some(workload_reference_values) }
    }

    /// Creates a new policy with reference values only for the platform
    /// certificate.
    pub(crate) fn new_unendorsed(root_certificate: Certificate) -> Self {
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
            self.workload_reference_values.as_ref().map(|ref_value| match ref_value {
                WorkloadReferenceValues::ImageReferenceValue(ref_value) => {
                    match &endorsement.workload_endorsement {
                        Some(workload_endorsement) => verify_endorsement_wrapper(
                            verification_time,
                            &image_reference,
                            workload_endorsement,
                            ref_value,
                        ),
                        None => {
                            Err(ConfidentialSpaceVerificationError::MissingWorkloadEndorsementError)
                        }
                    }
                }
                WorkloadReferenceValues::ContainerImageReferencePrefix(container_image_reference_prefix) => {
                    if image_reference.whole().starts_with(container_image_reference_prefix) {
                      Ok(())
                    } else {
                        Err(ConfidentialSpaceVerificationError::EndorsementContainerImageVerifyError{
                          actual: image_reference.whole(),
                          prefix: container_image_reference_prefix.clone(),
                        })
                    }
                }
            });

        let token_report = report_attestation_token(
            token,
            &self.root_certificate,
            &verification_time,
            OAK_SESSION_NOISE_V1_AUDIENCE.to_string(),
        );

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
        Endorsement, Event, Signature, SignedEndorsement, endorsement::Format,
    };
    use oak_time::make_instant;
    use prost::Message;
    use verify_endorsement::{
        create_endorsement_reference_value, create_signed_endorsement,
        create_verifying_key_from_pem,
    };
    use x509_cert::der::DecodePem;

    use super::*;
    use crate::jwt::verification::{CertificateReport, IssuerReport};

    // Note that this is strategically chosen to match (after hashing / base64
    // encoding) the "eat_nonce" values in testdata claims JSON files (or at
    // least those with valid "eat_nonce" values).
    const BINDING_KEY_BYTES: [u8; 32] = [
        0xad, 0x57, 0x5f, 0x38, 0x17, 0x7e, 0x11, 0x4a, 0x48, 0x2d, 0x5a, 0x24, 0x71, 0x28, 0x73,
        0x64, 0x27, 0x41, 0x53, 0x48, 0x51, 0x5b, 0x76, 0x78, 0x47, 0x11, 0x12, 0x43, 0x01, 0x61,
        0x64, 0x66,
    ];

    fn make_signed_endorsement(
        endorsement_filename: &str,
        signature_filename: &str,
        key_id: u32,
    ) -> SignedEndorsement {
        let serialized_endorsement = read_testdata!(endorsement_filename);
        let signature = read_testdata!(signature_filename);
        create_signed_endorsement(&serialized_endorsement, &signature, key_id, &[], &[])
    }

    fn create_reference_value(key_id: u32) -> BinaryReferenceValue {
        let developer_public_key_pem = read_testdata_string!("developer_key.pub.pem");
        let developer_public_key = create_verifying_key_from_pem(&developer_public_key_pem, key_id);
        let endorsement = create_endorsement_reference_value(developer_public_key, None);
        BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Endorsement(endorsement)),
        }
    }

    #[test]
    fn verify_endorsement_wrapper_success() {
        let verification_time = Instant::from_unix_seconds(1740000000);
        let image_reference: OciReference =
            "europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app@sha256:313b8a83d3c8bfc9abcffee4f538424473e2705383a7e46f16d159faf0e5ef34"
                .try_into()
                .unwrap();
        let signed_endorsement =
            make_signed_endorsement("endorsement.json", "endorsement_signature.sig", 1);
        let ref_value = create_reference_value(1);

        let result = verify_endorsement_wrapper(
            verification_time,
            &image_reference,
            &signed_endorsement,
            &ref_value,
        );

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn verify_endorsement_wrapper_invalid_signature_failure() {
        let verification_time = Instant::from_unix_seconds(1740000000);
        let image_reference: OciReference =
            "europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app@sha256:313b8a83d3c8bfc9abcffee4f538424473e2705383a7e46f16d159faf0e5ef34"
                .try_into()
                .unwrap();
        let signed_endorsement =
            make_signed_endorsement("endorsement.json", "other_endorsement_signature.sig", 1);
        let ref_value = create_reference_value(1);

        let result = verify_endorsement_wrapper(
            verification_time,
            &image_reference,
            &signed_endorsement,
            &ref_value,
        );

        assert!(result.is_err(), "Expected failure but got success");
    }

    #[test]
    fn verify_endorsement_wrapper_digest_success() {
        let verification_time = Instant::from_unix_seconds(1740000000);
        let digest_hex = "313b8a83d3c8bfc9abcffee4f538424473e2705383a7e46f16d159faf0e5ef34";
        let image_reference: OciReference = format!("europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app@sha256:{digest_hex}")
                .try_into()
                .unwrap();
        let ref_value = BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(
                oak_proto_rust::oak::attestation::v1::Digests {
                    digests: vec![oak_proto_rust::oak::RawDigest {
                        sha2_256: hex::decode(digest_hex).unwrap(),
                        ..Default::default()
                    }],
                },
            )),
        };

        let result = verify_endorsement_wrapper(
            verification_time,
            &image_reference,
            // The endorsement is ignored when verifying against digests.
            &SignedEndorsement::default(),
            &ref_value,
        );

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn verify_endorsement_wrapper_digest_failure() {
        let verification_time = Instant::from_unix_seconds(1740000000);
        let image_reference: OciReference =
            "europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app@sha256:313b8a83d3c8bfc9abcffee4f538424473e2705383a7e46f16d159faf0e5ef34"
                .try_into()
                .unwrap();
        let ref_value = BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(
                oak_proto_rust::oak::attestation::v1::Digests {
                    digests: vec![oak_proto_rust::oak::RawDigest {
                        // Wrong digest
                        sha2_256: hex::decode(
                            "313b8a83d3c8bfc9abcffee4f538424473e2705383a7e46f16d159faf0e5ef35",
                        )
                        .unwrap(),
                        ..Default::default()
                    }],
                },
            )),
        };

        let result = verify_endorsement_wrapper(
            verification_time,
            &image_reference,
            // The endorsement is ignored when verifying against digests.
            &SignedEndorsement::default(),
            &ref_value,
        );

        assert!(result.is_err(), "Expected failure but got success");
    }

    #[test]
    fn confidential_space_policy_verify_succeeds() {
        // The time has been set inside the validity interval of the test
        // token and the root certificate.
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let event = create_public_key_event(&BINDING_KEY_BYTES);

        let workload_endorsement = Some(SignedEndorsement {
            endorsement: Some(Endorsement {
                format: Format::EndorsementFormatJsonIntoto.into(),
                serialized: read_testdata!("endorsement.json"),
                ..Default::default()
            }),
            // The signature proto has a key ID which we do not use at the
            // moment.
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

        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");
        let root_certificate = Certificate::from_pem(&root_certificate_pem).unwrap();
        let ref_value = create_reference_value(0);
        let workload_ref_value = WorkloadReferenceValues::ImageReferenceValue(ref_value);
        let policy = ConfidentialSpacePolicy::new(root_certificate, workload_ref_value);

        let result = policy.verify(current_time, &event.encode_to_vec(), &endorsement.into());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn confidential_space_policy_report_succeeds() {
        // The time has been set inside the validity interval of the test
        // token and the root certificate.
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let event = create_public_key_event(&BINDING_KEY_BYTES);

        let signed_endorsement =
            make_signed_endorsement("endorsement.json", "endorsement_signature.sig", 0);
        let workload_endorsement = Some(signed_endorsement);
        let endorsement = ConfidentialSpaceEndorsement {
            jwt_token: read_testdata_string!("valid_token.jwt"),
            workload_endorsement,
        };

        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");
        let root_certificate = Certificate::from_pem(&root_certificate_pem).unwrap();
        let ref_value = create_reference_value(0);
        let workload_ref_value = WorkloadReferenceValues::ImageReferenceValue(ref_value);
        let policy = ConfidentialSpacePolicy::new(root_certificate, workload_ref_value);

        let result = policy.report(current_time, &event.encode_to_vec(), &endorsement.into());

        assert_matches!(
            result,
            Ok(ConfidentialSpaceVerificationReport {
                ref session_binding_public_key,
                public_key_verification: Ok(()),
                token_report: AttestationTokenVerificationReport {
                    has_required_claims: Ok(()),
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
                workload_endorsement_verification: Some(Ok(())),
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

        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");
        let root_certificate = Certificate::from_pem(&root_certificate_pem).unwrap();
        let policy = ConfidentialSpacePolicy::new_unendorsed(root_certificate);

        let result = policy.report(current_time, &event.encode_to_vec(), &endorsement.into());

        assert_matches!(
            result,
            Ok(ConfidentialSpaceVerificationReport {
                ref session_binding_public_key,
                public_key_verification: Ok(()),
                token_report: AttestationTokenVerificationReport {
                    has_required_claims: Ok(()),
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

    #[test]
    fn confidential_space_policy_verify_with_container_image_reference_succeeds() {
        // The time has been set inside the validity interval of the test
        // token and the root certificate.
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let event = create_public_key_event(&BINDING_KEY_BYTES);

        let endorsement = ConfidentialSpaceEndorsement {
            jwt_token: read_testdata_string!("valid_token.jwt"),
            workload_endorsement: None,
        };

        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");
        let root_certificate = Certificate::from_pem(&root_certificate_pem).unwrap();
        let container_image_reference_prefix =
            "europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app";
        let workload_ref_value = WorkloadReferenceValues::ContainerImageReferencePrefix(
            container_image_reference_prefix.to_string(),
        );
        let policy = ConfidentialSpacePolicy::new(root_certificate, workload_ref_value);

        let result = policy.verify(current_time, &event.encode_to_vec(), &endorsement.into());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn confidential_space_policy_verify_with_container_image_reference_fails() {
        // The time has been set inside the validity interval of the test
        // token and the root certificate.
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let event = create_public_key_event(&BINDING_KEY_BYTES);

        let endorsement = ConfidentialSpaceEndorsement {
            jwt_token: read_testdata_string!("valid_token.jwt"),
            workload_endorsement: None,
        };

        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");
        let root_certificate = Certificate::from_pem(&root_certificate_pem).unwrap();
        let container_image_reference_prefix =
            "europe-west2-docker.pkg.dev/oak-functions-standalone/oak-functions-containers";
        let workload_ref_value = WorkloadReferenceValues::ContainerImageReferencePrefix(
            container_image_reference_prefix.to_string(),
        );
        let policy = ConfidentialSpacePolicy::new(root_certificate, workload_ref_value);

        let result = policy.verify(current_time, &event.encode_to_vec(), &endorsement.into());

        assert!(result.is_err(), "Expected failure but got success");
    }

    #[test]
    fn confidential_space_policy_report_with_container_image_reference_succeeds() {
        // The time has been set inside the validity interval of the test
        // token and the root certificate.
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let event = create_public_key_event(&BINDING_KEY_BYTES);

        let endorsement = ConfidentialSpaceEndorsement {
            jwt_token: read_testdata_string!("valid_token.jwt"),
            workload_endorsement: None,
        };

        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");
        let root_certificate = Certificate::from_pem(&root_certificate_pem).unwrap();
        let container_image_reference_prefix =
            "europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app";
        let workload_ref_value = WorkloadReferenceValues::ContainerImageReferencePrefix(
            container_image_reference_prefix.to_string(),
        );
        let policy = ConfidentialSpacePolicy::new(root_certificate, workload_ref_value);

        let result = policy.report(current_time, &event.encode_to_vec(), &endorsement.into());

        assert_matches!(
            result,
            Ok(ConfidentialSpaceVerificationReport {
                workload_endorsement_verification: Some(Ok(())),
                ..
            })
        );
    }

    #[test]
    fn confidential_space_policy_report_with_container_image_reference_fails() {
        // The time has been set inside the validity interval of the test
        // token and the root certificate.
        let current_time = make_instant!("2025-07-01T17:31:32Z");

        let event = create_public_key_event(&BINDING_KEY_BYTES);

        let endorsement = ConfidentialSpaceEndorsement {
            jwt_token: read_testdata_string!("valid_token.jwt"),
            workload_endorsement: None,
        };

        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");
        let root_certificate = Certificate::from_pem(&root_certificate_pem).unwrap();
        let container_image_reference_prefix = "some/other/image";
        let workload_ref_value = WorkloadReferenceValues::ContainerImageReferencePrefix(
            container_image_reference_prefix.to_string(),
        );
        let policy = ConfidentialSpacePolicy::new(root_certificate, workload_ref_value);

        let result = policy.report(current_time, &event.encode_to_vec(), &endorsement.into());

        assert_matches!(
            result,
            Ok(ConfidentialSpaceVerificationReport {
                workload_endorsement_verification: Some(Err(
                    ConfidentialSpaceVerificationError::EndorsementContainerImageVerifyError { .. }
                )),
                ..
            })
        );
    }
}
