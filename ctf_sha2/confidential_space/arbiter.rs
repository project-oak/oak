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

use arbiter_rust_proto::oak::ctf_sha2::arbiter::{arbiter_input::TeeProof, ArbiterInput};
use clap::Parser;
use jwt::{Token, Unverified};
use log::{error, info};
use oak_attestation_gcp::{
    assertions::GcpAssertionVerifier,
    jwt::{Claims, Header},
    CONFIDENTIAL_SPACE_ROOT_CERT_PEM,
};
use oak_attestation_verification_types::assertion_verifier::AssertionVerifier;
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

fn main() -> anyhow::Result<()> {
    env_logger::init();

    falsify::falsify(falsify::FalsifyArgs::parse(), |input| {
        let input = match ArbiterInput::decode(input.as_slice()) {
            Ok(input) => input,
            Err(e) => {
                error!("Input failed to decode: {e}");
                return;
            }
        };

        let tee_proof = match input.tee_proof {
            Some(tee_proof) => tee_proof,
            None => {
                error!("Input does not contain tee_proof");
                return;
            }
        };

        let confidential_space_jwt = match tee_proof {
            TeeProof::ConfidentialSpaceJwt(confidential_space_jwt) => confidential_space_jwt,
            _ => {
                error!("Input does not contain confidential_space_jwt");
                return;
            }
        };

        let verifier = GcpAssertionVerifier {
            audience: OAK_CTF_SHA2_AUDIENCE.to_string(),
            reference_values: ConfidentialSpaceReferenceValues {
                root_certificate_pem: CONFIDENTIAL_SPACE_ROOT_CERT_PEM.to_string(),
                container_image: Some(ContainerImage::ImageReferenceValue(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![RawDigest {
                            sha2_256: hex::decode(EXPECTED_WORKLOAD_DIGEST).unwrap(),
                            ..Default::default()
                        }],
                    })),
                })),
            },
        };

        // Here we trust the JWT issuance timestamp. This is a bit circular, but there
        // is no obvious better alternative which results in deterministic behaviour.
        let now = Token::<Header, Claims, Unverified>::parse_unverified(&confidential_space_jwt)
            .unwrap()
            .claims()
            .issued_at;

        assert!(
            verifier
                .verify(
                    &Assertion {
                        content: ConfidentialSpaceAssertion {
                            jwt_token: confidential_space_jwt.into(),
                            container_image_endorsement: None,
                        }
                        .encode_to_vec(),
                    },
                    &input.flag,
                    now,
                )
                .inspect_err(|e| {
                    info!("JWT verification failed: {e:#}");
                })
                .is_err(),
            "JWT verification succeeded! Claim falsified."
        );
    });
    Ok(())
}
