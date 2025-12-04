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

#![feature(try_blocks)]

use anyhow::{anyhow, Context};
use arbiter_rust_proto::oak::ctf_sha2::arbiter::{arbiter_input::TeeProof, ArbiterInput};
use clap::Parser;
use jwt::{Token, Unverified};
use log::info;
use oak_attestation_gcp::{
    assertions::GcpAssertionVerifier,
    jwt::{Claims, Header},
    CONFIDENTIAL_SPACE_ROOT_CERT_PEM,
};
use oak_attestation_verification_types::assertion_verifier::{
    AssertionVerifier, AssertionVerifierError,
};
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, confidential_space_reference_values::ContainerImage, Assertion,
        BinaryReferenceValue, ConfidentialSpaceAssertion, ConfidentialSpaceReferenceValues,
        Digests,
    },
    RawDigest,
};
use prost::Message;

// See ctf_sha2/src/main.rs.
const OAK_CTF_SHA2_AUDIENCE: &str = "z08381475938604996746";

// Built at commit c9c0b847ea9e349ab8c8b797bab5e03d1762cb89:
// $ git checkout c9c0b847ea9e349ab8c8b797bab5e03d1762cb89 && \
//       bazel run ctf_sha2:image_push
const EXPECTED_WORKLOAD_DIGEST: &str =
    "692ab39ff6bd177481546e39179d40b961c2b5de7959f0ee388806050ac0244c";

fn main() {
    env_logger::init();

    falsify::falsify(
        falsify::FalsifyArgs::parse(),
        |input| -> Result<(), Box<dyn std::error::Error>> {
            let input = ArbiterInput::decode(input.as_slice())?;
            let tee_proof = input.tee_proof.context("Input does not contain tee_proof")?;
            let confidential_space_jwt = match tee_proof {
                TeeProof::ConfidentialSpaceJwt(confidential_space_jwt) => {
                    Ok(confidential_space_jwt)
                }
                _ => Err(anyhow!("Input does not contain confidential_space_jwt")),
            }?;
            assert!(
                verify_jwt(
                    confidential_space_jwt,
                    &input.flag,
                    confidential_space_reference_values(
                        CONFIDENTIAL_SPACE_ROOT_CERT_PEM.to_string(),
                        RawDigest {
                            sha2_256: hex::decode(EXPECTED_WORKLOAD_DIGEST)?,
                            ..Default::default()
                        }
                    )
                )
                .inspect_err(|e| {
                    info!("JWT verification failed: {e:#}");
                })
                .is_err(),
                "JWT verification succeeded! Claim falsified."
            );
            Ok(())
        },
    );
}

fn confidential_space_reference_values(
    pem: String,
    workload_digest: RawDigest,
) -> ConfidentialSpaceReferenceValues {
    ConfidentialSpaceReferenceValues {
        root_certificate_pem: pem,
        container_image: Some(ContainerImage::ImageReferenceValue(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![workload_digest],
            })),
        })),
    }
}

fn verify_jwt(
    confidential_space_jwt: String,
    asserted_flag: &[u8],
    reference_values: ConfidentialSpaceReferenceValues,
) -> Result<(), AssertionVerifierError> {
    // Here we trust the JWT issuance timestamp. This is not ideal because (if the
    // JWT is somehow forged by an attacker) then it is not trustworthy.
    // However, there is no obvious better alternative which results in
    // deterministic behaviour.
    let now = Token::<Header, Claims, Unverified>::parse_unverified(&confidential_space_jwt)
        .unwrap()
        .claims()
        .issued_at;

    GcpAssertionVerifier { audience: OAK_CTF_SHA2_AUDIENCE.to_string(), reference_values }.verify(
        &Assertion {
            content: ConfidentialSpaceAssertion {
                jwt_token: confidential_space_jwt.into(),
                container_image_endorsement: None,
            }
            .encode_to_vec(),
        },
        asserted_flag,
        now,
    )
}

#[cfg(test)]
mod tests {
    use base64::{engine::general_purpose::STANDARD, Engine};
    use jwt::{AlgorithmType, PKeyWithDigest, SignWithKey, SigningAlgorithm, Unsigned};
    use oak_time::{Duration, Instant};
    use openssl::{
        asn1::Asn1Time,
        hash::MessageDigest,
        pkey::{PKey, Private},
        rsa::Rsa,
        x509::X509,
    };
    use sha2::{Digest, Sha256};

    use super::*;

    #[test]
    fn test_verify_jwt_succeeds() -> anyhow::Result<()> {
        let now = oak_time_std::instant::now();
        let flag = b"here is a random flag";

        // Sign the JWT with the *expected* Confidential Space root certificate.
        let root_pkey = PKey::from_rsa(Rsa::generate(2048)?)?;
        let root_cert = self_signed_certificate(now, &root_pkey)?;
        let jwt = generate_token(&root_cert, now, flag, EXPECTED_WORKLOAD_DIGEST.to_string())?;
        let private_key = PKeyWithDigest { digest: MessageDigest::sha256(), key: root_pkey };
        let signed_jwt = jwt.sign_with_key(&Rs256PKeyWithDigest { delegate: private_key })?;

        assert!(verify_jwt(
            signed_jwt.as_str().to_string(),
            flag,
            confidential_space_reference_values(
                String::from_utf8(root_cert.to_pem()?)?,
                RawDigest {
                    sha2_256: hex::decode(EXPECTED_WORKLOAD_DIGEST)?,
                    ..Default::default()
                }
            )
        )
        .is_ok());

        Ok(())
    }

    #[test]
    fn test_verify_jwt_fails_invalid_signature() -> anyhow::Result<()> {
        let now = oak_time_std::instant::now();
        let flag = b"here is a random flag";

        // Sign the JWT with an *attacker* certificate.
        let attacker_pkey = PKey::from_rsa(Rsa::generate(2048)?)?;
        let attacker_cert = self_signed_certificate(now, &attacker_pkey)?;
        let jwt = generate_token(&attacker_cert, now, flag, EXPECTED_WORKLOAD_DIGEST.to_string())?;
        let private_key = PKeyWithDigest { digest: MessageDigest::sha256(), key: attacker_pkey };
        let signed_jwt = jwt.sign_with_key(&Rs256PKeyWithDigest { delegate: private_key })?;

        assert!(verify_jwt(
            signed_jwt.as_str().to_string(),
            flag,
            confidential_space_reference_values(
                CONFIDENTIAL_SPACE_ROOT_CERT_PEM.to_string(),
                RawDigest {
                    sha2_256: hex::decode(EXPECTED_WORKLOAD_DIGEST)?,
                    ..Default::default()
                }
            )
        )
        .is_err());

        Ok(())
    }

    #[test]
    fn test_verify_jwt_fails_invalid_flag() -> anyhow::Result<()> {
        let now = oak_time_std::instant::now();

        // Sign the JWT with the *expected* Confidential Space root certificate.
        let root_pkey = PKey::from_rsa(Rsa::generate(2048)?)?;
        let root_cert = self_signed_certificate(now, &root_pkey)?;
        let jwt = generate_token(
            &root_cert,
            now,
            b"here is a random flag",
            EXPECTED_WORKLOAD_DIGEST.to_string(),
        )?;
        let private_key = PKeyWithDigest { digest: MessageDigest::sha256(), key: root_pkey };
        let signed_jwt = jwt.sign_with_key(&Rs256PKeyWithDigest { delegate: private_key })?;

        assert!(verify_jwt(
            signed_jwt.as_str().to_string(),
            // Supply a different flag than the one that Confidential Space signed.
            b"this is a bad guess",
            confidential_space_reference_values(
                String::from_utf8(root_cert.to_pem()?)?,
                RawDigest {
                    sha2_256: hex::decode(EXPECTED_WORKLOAD_DIGEST)?,
                    ..Default::default()
                }
            )
        )
        .is_err());

        Ok(())
    }

    #[test]
    fn test_verify_jwt_fails_incorrect_workload() -> anyhow::Result<()> {
        let now = oak_time_std::instant::now();
        let flag = b"here is a random flag";

        // Sign the JWT with the *expected* Confidential Space root certificate.
        let root_pkey = PKey::from_rsa(Rsa::generate(2048)?)?;
        let root_cert = self_signed_certificate(now, &root_pkey)?;
        let jwt = generate_token(
            &root_cert,
            now,
            flag,
            // Generate the JWT in an attacker workload.
            hex::encode(Sha256::digest(b"attacker workload!")),
        )?;
        let private_key = PKeyWithDigest { digest: MessageDigest::sha256(), key: root_pkey };
        let signed_jwt = jwt.sign_with_key(&Rs256PKeyWithDigest { delegate: private_key })?;

        assert!(verify_jwt(
            signed_jwt.as_str().to_string(),
            flag,
            confidential_space_reference_values(
                String::from_utf8(root_cert.to_pem()?)?,
                RawDigest {
                    sha2_256: hex::decode(EXPECTED_WORKLOAD_DIGEST)?,
                    ..Default::default()
                }
            )
        )
        .is_err());

        Ok(())
    }

    fn self_signed_certificate(now: Instant, pkey: &PKey<Private>) -> anyhow::Result<X509> {
        let mut builder = X509::builder()?;
        builder.set_pubkey(pkey)?;
        let not_before = Asn1Time::from_unix((now - Duration::from_hours(1)).into_unix_seconds())?;
        builder.set_not_before(&not_before)?;
        let not_after = Asn1Time::from_unix((now + Duration::from_hours(1)).into_unix_seconds())?;
        builder.set_not_after(&not_after)?;
        builder.sign(pkey, MessageDigest::sha256())?;
        Ok(builder.build())
    }

    fn generate_token(
        root_cert: &X509,
        now: Instant,
        flag: &[u8],
        workload_digest_hex: String,
    ) -> anyhow::Result<Token<Header, Claims, Unsigned>> {
        Ok(Token::new(
            Header {
                algorithm: jwt::AlgorithmType::Rs256,
                x509_chain: vec![STANDARD.encode(root_cert.to_der()?)],
            },
            Claims {
                audience: OAK_CTF_SHA2_AUDIENCE.to_string(),
                eat_nonce: hex::encode(Sha256::digest(flag)),
                issued_at: now,
                not_before: now - Duration::from_hours(1),
                not_after: now + Duration::from_hours(1),
                submods: oak_attestation_gcp::jwt::Submods {
                    confidential_space: oak_attestation_gcp::jwt::ConfidentialSpaceClaims {
                        support_attributes: vec!["STABLE".to_string()],
                    },
                    container: oak_attestation_gcp::jwt::ContainerClaims {
                        image_reference: "gcr.io/oak-ci/oak-containers-system-image".to_string(),
                        image_digest: "sha256:".to_owned() + &workload_digest_hex,
                        ..Default::default()
                    },
                },
                debug_status: "disabled-since-boot".to_string(),
                software_name: "CONFIDENTIAL_SPACE".to_string(),
                ..Default::default()
            },
        ))
    }

    // This is a hack copied from `oak_attestation_verification_cli/src/report.rs`
    // to work around an issue with the jwt crate.
    struct Rs256PKeyWithDigest<T> {
        delegate: PKeyWithDigest<T>,
    }

    impl SigningAlgorithm for Rs256PKeyWithDigest<openssl::pkey::Private> {
        fn algorithm_type(&self) -> AlgorithmType {
            AlgorithmType::Rs256
        }
        fn sign(&self, header: &str, claims: &str) -> Result<String, jwt::error::Error> {
            self.delegate.sign(header, claims)
        }
    }
}
