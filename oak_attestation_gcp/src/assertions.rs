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

use alloc::string::String;

use anyhow::{anyhow, Context};
use jwt::Token;
use oak_attestation_types::assertion_generator::{AssertionGenerator, AssertionGeneratorError};
use oak_attestation_verification_types::assertion_verifier::{
    AssertionVerifier, AssertionVerifierError,
};
use oak_proto_rust::oak::attestation::v1::{
    confidential_space_reference_values::ContainerImage, Assertion, ConfidentialSpaceAssertion,
    ConfidentialSpaceEndorsement, ConfidentialSpaceReferenceValues, EndorsementReferenceValue,
};
use oak_time::Instant;
use oci_spec::distribution::Reference;
use prost::Message;
use sha2::Digest;
use verify_endorsement::create_endorsement_reference_value;
use x509_cert::{der::DecodePem, Certificate};

use crate::{
    jwt::{verification::report_attestation_token, Claims, Header},
    policy::{verify_endorsement_wrapper, ConfidentialSpaceVerificationError},
};

#[allow(dead_code)]
pub struct GcpAssertionGenerator {
    pub audience: String,
    pub endorsement: Option<ConfidentialSpaceEndorsement>,
}

impl GcpAssertionGenerator {
    pub fn new(audience: String, endorsement: Option<ConfidentialSpaceEndorsement>) -> Self {
        Self { audience, endorsement }
    }
}

fn generate_nonce_from_asserted_data(data: &[u8]) -> String {
    let digest = sha2::Sha256::digest(data);
    hex::encode(digest)
}

impl AssertionGenerator for GcpAssertionGenerator {
    fn generate(&self, data: &[u8]) -> Result<Assertion, AssertionGeneratorError> {
        let nonce = generate_nonce_from_asserted_data(data);
        let token = crate::attestation::request_attestation_token(&self.audience, &nonce)
            .context("requesting attestation token")?;
        let assertion = ConfidentialSpaceAssertion {
            jwt_token: token.into(),
            container_image_endorsement: self.endorsement.clone(),
        };

        Ok(Assertion { content: assertion.encode_to_vec() })
    }
}

#[allow(dead_code)]
pub struct GcpAssertionVerifier {
    pub audience: String,
    pub reference_values: ConfidentialSpaceReferenceValues,
}

impl GcpAssertionVerifier {
    #[allow(dead_code)]
    fn verify_endorsed_container_image(
        &self,
        verification_time: Instant,
        image_reference: &Reference,
        endorsement_reference_value: &EndorsementReferenceValue,
        endorsement: &Option<ConfidentialSpaceEndorsement>,
    ) -> Result<(), AssertionVerifierError> {
        match endorsement {
            Some(ci_endorsement) => match &ci_endorsement.workload_endorsement {
                Some(signed_endorsement) => verify_endorsement_wrapper(
                    verification_time,
                    image_reference,
                    signed_endorsement,
                    endorsement_reference_value,
                )
                .context("verifying workload endorsement")?,
                None => return Err(anyhow!("missing workload endorsement").into()),
            },
            None => {
                return Err(anyhow!(
                    "reference values require endorsement to be provided but none was given"
                )
                .into())
            }
        }
        Ok(())
    }
}

impl AssertionVerifier for GcpAssertionVerifier {
    fn verify(
        &self,
        assertion: &Assertion,
        asserted_data: &[u8],
        verification_time: Instant,
    ) -> Result<(), AssertionVerifierError> {
        let cs_assertion = ConfidentialSpaceAssertion::decode(assertion.content.as_slice())
            .context("parsing ConfidentialSpaceAssertion")?;
        let jwt = String::from_utf8(cs_assertion.jwt_token.clone())
            .context("decoding JWT token as UTF-8 string")?;
        let token: Token<Header, Claims, _> =
            Token::parse_unverified(&jwt).context("parsing the JWT token")?;

        let root_certificate =
            Certificate::from_pem(&self.reference_values.root_certificate_pem)
                .map_err(|e| anyhow!("failed to parse the root certificate: {e:?}"))?;

        let image_reference = token
            .claims()
            .effective_reference()
            .context("parsing the effective OCI container reference")?;
        if let Some(ci_ref_value) = &self.reference_values.container_image {
            match ci_ref_value {
                ContainerImage::CosignReferenceValues(cosign_reference_values) => {
                    let endorser_key = cosign_reference_values
                        .developer_public_key
                        .as_ref()
                        .ok_or(anyhow::anyhow!("endorser public key missing"))?
                        .clone();
                    let rekor_key = cosign_reference_values.rekor_public_key.clone();
                    let endorsement_ref_value =
                        create_endorsement_reference_value(endorser_key, rekor_key);
                    self.verify_endorsed_container_image(
                        verification_time,
                        &image_reference,
                        &endorsement_ref_value,
                        &cs_assertion.container_image_endorsement,
                    )?;
                }
                ContainerImage::ContainerImageReferencePrefix(ci_reference_prefix) => {
                    if !image_reference.whole().starts_with(ci_reference_prefix) {
                        return Err(anyhow!(
                        ConfidentialSpaceVerificationError::EndorsementContainerImageVerifyError {
                            actual: image_reference.whole(),
                            prefix: ci_reference_prefix.clone(),
                        })
                        .into());
                    }
                }
                ContainerImage::EndorsementReferenceValues(endorsement_ref_value) => {
                    self.verify_endorsed_container_image(
                        verification_time,
                        &image_reference,
                        endorsement_ref_value,
                        &cs_assertion.container_image_endorsement,
                    )?;
                }
            }
        }

        let expected_nonce = generate_nonce_from_asserted_data(asserted_data);
        let eat_nonce = token.claims().eat_nonce.clone();
        let token_report = report_attestation_token(
            token,
            &root_certificate,
            &verification_time,
            self.audience.clone(),
        );
        token_report.has_required_claims.context("checking the GCP JWT token required claims")?;
        token_report.validity.context("checking the GCP JWT token validity period")?;
        token_report.verification.context("checking the GCP JWT token verification status")?;
        token_report.issuer_report.context("checking the GCP JWT token issuer root signature")?;

        if eat_nonce != expected_nonce {
            return Err(AssertionVerifierError::AssertedDataMismatch {
                expected: expected_nonce,
                actual: eat_nonce,
            });
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Ok;
    use oak_attestation_verification_types::assertion_verifier::AssertionVerifierError;
    use oak_file_utils::{read_testdata, read_testdata_string};
    use oak_proto_rust::oak::attestation::v1::{
        endorsement::Format, CosignReferenceValues, Endorsement, Signature, SignedEndorsement,
    };
    use oak_time::make_instant;
    use prost::Message;
    use verify_endorsement::create_verifying_key_from_pem;

    use super::*;
    use crate::OAK_SESSION_NOISE_V1_AUDIENCE;

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
    ) -> SignedEndorsement {
        SignedEndorsement {
            endorsement: Some(Endorsement {
                format: Format::EndorsementFormatJsonIntoto.into(),
                serialized: read_testdata!(endorsement_filename),
                ..Default::default()
            }),
            signature: Some(Signature {
                raw: read_testdata!(signature_filename),
                ..Default::default()
            }),
            ..Default::default()
        }
    }

    #[test]
    fn verify_succeeds_with_endorsement() -> anyhow::Result<()> {
        let developer_public_key_pem = read_testdata_string!("developer_key.pub.pem");
        let developer_public_key = create_verifying_key_from_pem(&developer_public_key_pem, 0);
        let verifier = GcpAssertionVerifier {
            audience: OAK_SESSION_NOISE_V1_AUDIENCE.to_string(),
            reference_values: ConfidentialSpaceReferenceValues {
                root_certificate_pem: read_testdata_string!("root_ca_cert.pem"),
                container_image: Some(ContainerImage::EndorsementReferenceValues(
                    create_endorsement_reference_value(developer_public_key, None),
                )),
            },
        };

        let assertion = Assertion {
            content: ConfidentialSpaceAssertion {
                jwt_token: read_testdata!("valid_token.jwt"),
                container_image_endorsement: Some(ConfidentialSpaceEndorsement {
                    workload_endorsement: Some(make_signed_endorsement(
                        "endorsement.json",
                        "endorsement_signature.sig",
                    )),
                    ..Default::default()
                }),
            }
            .encode_to_vec(),
        };

        verifier.verify(&assertion, &BINDING_KEY_BYTES, make_instant!("2025-07-01T17:31:32Z"))?;
        Ok(())
    }

    #[test]
    fn verify_succeeds_with_container_image_prefix() -> anyhow::Result<()> {
        let verifier = GcpAssertionVerifier {
            audience: OAK_SESSION_NOISE_V1_AUDIENCE.to_string(),
            reference_values: ConfidentialSpaceReferenceValues {
                root_certificate_pem: read_testdata_string!("root_ca_cert.pem"),
                container_image: Some(ContainerImage::ContainerImageReferencePrefix(
                    "europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app"
                        .to_string(),
                )),
            },
        };

        let assertion = Assertion {
            content: ConfidentialSpaceAssertion {
                jwt_token: read_testdata!("valid_token.jwt"),
                container_image_endorsement: None,
            }
            .encode_to_vec(),
        };

        verifier.verify(&assertion, &BINDING_KEY_BYTES, make_instant!("2025-07-01T17:31:32Z"))?;
        Ok(())
    }

    #[test]
    fn verify_fails_with_mismatched_asserted_data() {
        let verifier = GcpAssertionVerifier {
            audience: OAK_SESSION_NOISE_V1_AUDIENCE.to_string(),
            reference_values: ConfidentialSpaceReferenceValues {
                root_certificate_pem: read_testdata_string!("root_ca_cert.pem"),
                container_image: None,
            },
        };

        let assertion = Assertion {
            content: ConfidentialSpaceAssertion {
                jwt_token: read_testdata!("valid_token.jwt"),
                container_image_endorsement: None,
            }
            .encode_to_vec(),
        };

        let result = verifier.verify(
            &assertion,
            b"invalid asserted data",
            make_instant!("2025-07-01T17:31:32Z"),
        );
        assert!(matches!(result, Err(AssertionVerifierError::AssertedDataMismatch { .. })));
    }

    #[test]
    fn verify_fails_with_invalid_jwt() {
        let verifier = GcpAssertionVerifier {
            audience: OAK_SESSION_NOISE_V1_AUDIENCE.to_string(),
            reference_values: ConfidentialSpaceReferenceValues {
                root_certificate_pem: read_testdata_string!("root_ca_cert.pem"),
                container_image: None,
            },
        };

        let assertion = Assertion {
            content: ConfidentialSpaceAssertion {
                jwt_token: read_testdata!("invalid_signature_token.jwt"),
                container_image_endorsement: None,
            }
            .encode_to_vec(),
        };

        let result =
            verifier.verify(&assertion, &BINDING_KEY_BYTES, make_instant!("2025-07-01T17:31:32Z"));
        assert!(result.is_err());
    }

    #[test]
    fn verify_fails_with_missing_endorsement() {
        let verifier = GcpAssertionVerifier {
            audience: OAK_SESSION_NOISE_V1_AUDIENCE.to_string(),
            reference_values: ConfidentialSpaceReferenceValues {
                root_certificate_pem: read_testdata_string!("root_ca_cert.pem"),
                container_image: Some(ContainerImage::CosignReferenceValues(
                    CosignReferenceValues {
                        developer_public_key: Some(create_verifying_key_from_pem(
                            &read_testdata_string!("developer_key.pub.pem"),
                            1,
                        )),
                        rekor_public_key: None,
                    },
                )),
            },
        };

        let assertion = Assertion {
            content: ConfidentialSpaceAssertion {
                jwt_token: read_testdata!("valid_token.jwt"),
                container_image_endorsement: None,
            }
            .encode_to_vec(),
        };

        let result =
            verifier.verify(&assertion, &BINDING_KEY_BYTES, make_instant!("2025-07-01T17:31:32Z"));
        assert!(result.is_err());
    }

    #[test]
    fn verify_fails_with_invalid_endorsement() {
        let verifier = GcpAssertionVerifier {
            audience: OAK_SESSION_NOISE_V1_AUDIENCE.to_string(),
            reference_values: ConfidentialSpaceReferenceValues {
                root_certificate_pem: read_testdata_string!("root_ca_cert.pem"),
                container_image: Some(ContainerImage::CosignReferenceValues(
                    CosignReferenceValues {
                        developer_public_key: Some(create_verifying_key_from_pem(
                            &read_testdata_string!("developer_key.pub.pem"),
                            1,
                        )),
                        rekor_public_key: None,
                    },
                )),
            },
        };

        let assertion = Assertion {
            content: ConfidentialSpaceAssertion {
                jwt_token: read_testdata!("valid_token.jwt"),
                container_image_endorsement: Some(ConfidentialSpaceEndorsement {
                    workload_endorsement: Some(make_signed_endorsement(
                        "endorsement.json",
                        "other_endorsement_signature.sig",
                    )),
                    ..Default::default()
                }),
            }
            .encode_to_vec(),
        };

        let result =
            verifier.verify(&assertion, &BINDING_KEY_BYTES, make_instant!("2025-07-01T17:31:32Z"));
        assert!(result.is_err());
    }

    #[test]
    fn verify_fails_with_mismatched_container_image_prefix() {
        let verifier = GcpAssertionVerifier {
            audience: OAK_SESSION_NOISE_V1_AUDIENCE.to_string(),
            reference_values: ConfidentialSpaceReferenceValues {
                root_certificate_pem: read_testdata_string!("root_ca_cert.pem"),
                container_image: Some(ContainerImage::ContainerImageReferencePrefix(
                    "some/other/image".to_string(),
                )),
            },
        };

        let assertion = Assertion {
            content: ConfidentialSpaceAssertion {
                jwt_token: read_testdata!("valid_token.jwt"),
                container_image_endorsement: None,
            }
            .encode_to_vec(),
        };

        let result =
            verifier.verify(&assertion, &BINDING_KEY_BYTES, make_instant!("2025-07-01T17:31:32Z"));
        assert!(result.is_err());
    }
}
