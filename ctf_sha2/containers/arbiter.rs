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

use anyhow::{anyhow, Context};
use arbiter_rust_proto::oak::ctf_sha2::arbiter::{
    arbiter_input::TeeProof, ArbiterInput, AttestedSignature,
};
use clap::Parser;
use log::info;
use oak_attestation_verification::verifier::verify;
use oak_proto_rust::oak::attestation::v1::{
    binary_reference_value, kernel_binary_reference_value, reference_values,
    tcb_version_reference_value, text_reference_value, AmdSevReferenceValues, BinaryReferenceValue,
    ContainerLayerReferenceValues, Digests, Endorsements, KernelBinaryReferenceValue,
    KernelDigests, KernelLayerReferenceValues, OakContainersReferenceValues, ReferenceValues,
    RootLayerReferenceValues, StringLiterals, SystemLayerReferenceValues, TcbVersion,
    TcbVersionReferenceValue, TextReferenceValue,
};
use oak_time::Instant;
use p256::ecdsa::VerifyingKey;
use prost::Message;
use sha2::{Digest, Sha256};
use x509_cert::{der::Decode, spki::EncodePublicKey, Certificate};

fn main() {
    env_logger::init();

    falsify::falsify(
        falsify::FalsifyArgs::parse(),
        |input| -> Result<(), Box<dyn std::error::Error>> {
            let input = ArbiterInput::decode(input.as_slice())?;
            let tee_proof = input.tee_proof.context("Input does not contain tee_proof")?;
            let attested_signature = match tee_proof {
                TeeProof::AttestedSignature(attested_signature) => Ok(attested_signature),
                _ => Err(anyhow!("Input does not contain attested_signature")),
            }?;

            // Here we trust the VCEK "not before" timestamp. This is not ideal because (if
            // the cert is somehow forged by an attacker) then it is not
            // trustworthy. However, there is no obvious better alternative
            // which results in deterministic behaviour.
            let endorsements = attested_signature
                .endorsements
                .as_ref()
                .context("Input does not contain enclave endorsements")?;
            let vcek_cert_not_before = vcek_cert_not_before(endorsements)?;

            assert!(
                verify_attested_signature(
                    &vcek_cert_not_before,
                    &attested_signature,
                    &input.flag,
                    &create_reference_values()
                )
                .inspect_err(|e| {
                    info!("Enclave signature verification failed: {e:#}");
                })
                .is_err(),
                "Signature verification succeeded! Claim falsified."
            );
            Ok(())
        },
    );
}

fn verify_attested_signature(
    now: &Instant,
    attested_signature: &AttestedSignature,
    asserted_flag: &[u8],
    reference_values: &ReferenceValues,
) -> anyhow::Result<()> {
    // Verify Evidence
    let evidence =
        attested_signature.evidence.as_ref().context("Input does not contain enclave evidence")?;
    let endorsements = attested_signature
        .endorsements
        .as_ref()
        .context("Input does not contain enclave endorsements")?;
    let extracted = verify(now.into_unix_millis(), evidence, endorsements, reference_values)?;

    // Verify signature over expected flag digest
    key_util::verify_signature_ecdsa(
        &attested_signature.signature,
        &Sha256::digest(asserted_flag),
        VerifyingKey::from_sec1_bytes(&extracted.signing_public_key)
            .map_err(|e| anyhow::anyhow!("failed to parse public key: {e}"))?
            .to_public_key_der()
            .map_err(|e| anyhow::anyhow!("failed to convert public key to DER: {e}"))?
            .as_bytes(),
    )
}

fn vcek_cert_not_before(endorsements: &Endorsements) -> anyhow::Result<Instant> {
    let vcek_cert = match &endorsements.r#type {
        Some(oak_proto_rust::oak::attestation::v1::endorsements::Type::OakContainers(
            oak_proto_rust::oak::attestation::v1::OakContainersEndorsements {
                root_layer:
                    Some(oak_proto_rust::oak::attestation::v1::RootLayerEndorsements {
                        tee_certificate: vcek_cert,
                        ..
                    }),
                ..
            },
        )) => vcek_cert,
        _ => return Err(anyhow::anyhow!("Endorsements does not contain VCEK certificate")),
    };
    let not_before = Certificate::from_der(vcek_cert.as_slice())
        .map_err(|e| anyhow::anyhow!("failed to parse VCEK certificate: {e}"))?
        .tbs_certificate
        .validity
        .not_before;
    Ok(Instant::from_unix_millis(not_before.to_unix_duration().as_millis() as i64))
}

fn create_reference_values() -> ReferenceValues {
    ReferenceValues {
        r#type: Some(reference_values::Type::OakContainers(OakContainersReferenceValues {
            root_layer: Some(RootLayerReferenceValues {
                amd_sev: Some(AmdSevReferenceValues {
                    genoa: Some(TcbVersionReferenceValue {
                        r#type: Some(tcb_version_reference_value::Type::Minimum(TcbVersion {
                            boot_loader: 10,
                            tee: 0,
                            snp: 25,
                            microcode: 84,
                            fmc: 0
                        }))
                    }),
                    allow_debug: false,
                    stage0: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(Digests {
                            digests: vec![raw_digests::sha2_384("5e517290a2a214e23645051ff20e0f4db81320239660cca4d3e6d90d065df60caad32a31445fdd3123353c5cc7262944")]
                        }))
                    }),
                    check_vcek_cert_expiry: true,
                    ..Default::default()
                }),
                ..Default::default()
            }),
            kernel_layer: Some(KernelLayerReferenceValues {
                kernel: Some(KernelBinaryReferenceValue {
                    r#type: Some(kernel_binary_reference_value::Type::Digests(KernelDigests {
                        image: Some(Digests {
                            digests: vec![raw_digests::sha2_256("f9d0584247b46cc234a862aa8cd08765b38405022253a78b9af189c4cedbe447")]
                        }),
                        setup_data: Some(Digests {
                            digests: vec![raw_digests::sha2_256("75f091da89ce81e9decb378c3b72a948aed5892612256b3a6e8305ed034ec39a")]
                        })
                    }))
                }),
                kernel_cmd_line_text: Some(TextReferenceValue {
                    r#type: Some(text_reference_value::Type::StringLiterals(StringLiterals { value: vec![" console=ttyS0 panic=-1 brd.rd_nr=1 brd.rd_size=3000000 brd.max_part=1 ip=10.0.2.15:::255.255.255.0::eth0:off loglevel=7 -- --launcher-addr=vsock://2:32823".to_string()] }))
                }),
                init_ram_fs: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![raw_digests::sha2_256("fbafce2712953d6c5d918f95f9c21cdf32f10e59895e766718b2af7d60b160f3")]
                    }))
                }),
                memory_map: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![raw_digests::sha2_256("b0c0a40c5313464c5c507f618beca9abbd4ceb98a984377c71968320204885b0")]
                    }))
                }),
                acpi: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![raw_digests::sha2_256("2e0f3b840e4f9fdc6556ba8b763667aa07a424f7aac0f86b08090378de3bd669")]
                    }))
                })
            }),
            system_layer: Some(SystemLayerReferenceValues {
                system_image: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![raw_digests::sha2_256("c2b393fa58a36952ecf7a4eb346874c46c4b0b54dc658b274cf3767350e3e44f")]
                    }))
                })
            }),
            container_layer: Some(ContainerLayerReferenceValues {
                binary: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![raw_digests::sha2_256("6f75556f586e18faa3c4cffd1bcb46ae7f701d978c069043e1e520898cd14d4c")]
                    }))
                }),
                configuration: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![raw_digests::sha2_256("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")]
                    }))
                })
            })
        }))
    }
}

mod raw_digests {
    use oak_proto_rust::oak::RawDigest;

    pub fn sha2_256(digest: &str) -> RawDigest {
        RawDigest { sha2_256: hex::decode(digest).unwrap(), ..Default::default() }
    }

    pub fn sha2_384(digest: &str) -> RawDigest {
        RawDigest { sha2_384: hex::decode(digest).unwrap(), ..Default::default() }
    }
}

#[cfg(test)]
mod tests {
    use coset::{cbor::value::Value, cwt::ClaimName, CborSerializable, CoseKey};
    use oak_dice::cert::{CONTAINER_IMAGE_LAYER_ID, KERNEL_LAYER_ID, SYSTEM_IMAGE_LAYER_ID};
    use oak_proto_rust::oak::attestation::v1::{
        binary_reference_value, kernel_binary_reference_value, reference_values,
        text_reference_value, ApplicationKeys, BinaryReferenceValue, ContainerLayerReferenceValues,
        Endorsements, Evidence, KernelBinaryReferenceValue, KernelLayerReferenceValues,
        LayerEvidence, OakContainersEndorsements, OakContainersReferenceValues, ReferenceValues,
        RootLayerEndorsements, RootLayerEvidence, RootLayerReferenceValues,
        SystemLayerReferenceValues, TeePlatform, TextReferenceValue,
    };
    use oak_time::make_instant;
    use p256::ecdsa::{signature::Signer, SigningKey};
    use sha2::{Digest, Sha256};

    use super::*;

    #[test]
    fn test_verify_attested_signature_succeeds() {
        let (evidence, signing_key) = generate_fake_evidence();
        let flag = b"here is a random flag";
        let signature: p256::ecdsa::Signature = signing_key.sign(&Sha256::digest(flag));

        assert!(verify_attested_signature(
            &make_instant!("2025-12-09T09:04:07.000Z"),
            &AttestedSignature {
                evidence: Some(evidence),
                endorsements: Some(empty_endorsements()),
                signature: signature.to_der().to_bytes().to_vec(),
            },
            flag,
            &insecure_reference_values()
        )
        .is_ok());
    }

    #[test]
    fn test_verify_attested_signature_fails_invalid_signature() {
        let (evidence, _signing_key) = generate_fake_evidence();
        let flag = b"here is a random flag";

        assert!(verify_attested_signature(
            &make_instant!("2025-12-09T09:04:07.000Z"),
            &AttestedSignature {
                evidence: Some(evidence),
                endorsements: Some(empty_endorsements()),
                // Provide an invalid signature
                signature: vec![0u8; 64],
            },
            flag,
            &insecure_reference_values()
        )
        .is_err());
    }

    #[test]
    fn test_verify_attested_signature_fails_invalid_flag() {
        let (evidence, signing_key) = generate_fake_evidence();
        let flag = b"here is a random flag";
        let signature: p256::ecdsa::Signature = signing_key.sign(&Sha256::digest(flag));

        assert!(verify_attested_signature(
            &make_instant!("2025-12-09T09:04:07.000Z"),
            &AttestedSignature {
                evidence: Some(evidence),
                endorsements: Some(empty_endorsements()),
                signature: signature.to_der().to_bytes().to_vec(),
            },
            // Supply a different flag than the one that the enclave app signed.
            b"this is a bad guess",
            &insecure_reference_values()
        )
        .is_err());
    }

    fn generate_fake_evidence() -> (Evidence, SigningKey) {
        // 1. Generate Root Key
        let (root_private_key, root_public_key) = oak_dice::cert::generate_ecdsa_key_pair();

        // 2. Create Fake Root Report
        let root_public_key_cose = oak_dice::cert::verifying_key_to_cose_key(&root_public_key);
        let root_layer = RootLayerEvidence {
            platform: TeePlatform::None.into(),
            remote_attestation_report: create_fake_attestation_report(root_public_key_cose.clone()),
            eca_public_key: root_public_key_cose
                .to_vec()
                .expect("failed to serialize root public key"),
        };

        // 3. Create Layer 1 (Kernel)
        let (kernel_private_key, kernel_public_key) = oak_dice::cert::generate_ecdsa_key_pair();

        // Populate required claims with dummy values
        let kernel_claims = vec![(
            ClaimName::PrivateUse(KERNEL_LAYER_ID),
            Value::Map(vec![
                (
                    Value::Integer(oak_dice::cert::KERNEL_MEASUREMENT_ID.into()),
                    Value::Map(vec![(
                        Value::Integer(oak_dice::cert::SHA2_256_ID.into()),
                        Value::Bytes(vec![0u8; 32]),
                    )]),
                ),
                (
                    Value::Integer(oak_dice::cert::KERNEL_COMMANDLINE_ID.into()),
                    Value::Text("console=ttyS0".to_string()),
                ),
                (
                    Value::Integer(oak_dice::cert::SETUP_DATA_MEASUREMENT_ID.into()),
                    Value::Map(vec![(
                        Value::Integer(oak_dice::cert::SHA2_256_ID.into()),
                        Value::Bytes(vec![0u8; 32]),
                    )]),
                ),
                (
                    Value::Integer(oak_dice::cert::INITRD_MEASUREMENT_ID.into()),
                    Value::Map(vec![(
                        Value::Integer(oak_dice::cert::SHA2_256_ID.into()),
                        Value::Bytes(vec![0u8; 32]),
                    )]),
                ),
                (
                    Value::Integer(oak_dice::cert::MEMORY_MAP_MEASUREMENT_ID.into()),
                    Value::Map(vec![(
                        Value::Integer(oak_dice::cert::SHA2_256_ID.into()),
                        Value::Bytes(vec![0u8; 32]),
                    )]),
                ),
                (
                    Value::Integer(oak_dice::cert::ACPI_MEASUREMENT_ID.into()),
                    Value::Map(vec![(
                        Value::Integer(oak_dice::cert::SHA2_256_ID.into()),
                        Value::Bytes(vec![0u8; 32]),
                    )]),
                ),
            ]),
        )];

        let kernel_cert = oak_dice::cert::generate_signing_certificate(
            &root_private_key,
            hex::encode(oak_dice::cert::derive_verifying_key_id(&root_public_key)),
            &kernel_public_key,
            kernel_claims,
        )
        .expect("failed to generate kernel certificate");

        // 4. Create Layer 2 (System)
        let (system_private_key, system_public_key) = oak_dice::cert::generate_ecdsa_key_pair();

        let system_claims = vec![(
            ClaimName::PrivateUse(SYSTEM_IMAGE_LAYER_ID),
            Value::Map(vec![(
                Value::Integer(oak_dice::cert::LAYER_2_CODE_MEASUREMENT_ID.into()),
                Value::Map(vec![(
                    Value::Integer(oak_dice::cert::SHA2_256_ID.into()),
                    Value::Bytes(vec![0u8; 32]),
                )]),
            )]),
        )];

        let system_cert = oak_dice::cert::generate_signing_certificate(
            &kernel_private_key,
            hex::encode(oak_dice::cert::derive_verifying_key_id(&kernel_public_key)),
            &system_public_key,
            system_claims,
        )
        .expect("failed to generate system certificate");

        // 5. Create Application Keys (signed by System Key, containing Container
        //    Claims)
        let app_encryption_public_key_bytes = vec![0u8; 32]; // Fake X25519 key

        let (app_signing_private_key, app_signing_public_key) =
            oak_dice::cert::generate_ecdsa_key_pair();

        let container_claims = vec![(
            ClaimName::PrivateUse(CONTAINER_IMAGE_LAYER_ID),
            Value::Map(vec![
                (
                    Value::Integer(oak_dice::cert::LAYER_3_CODE_MEASUREMENT_ID.into()),
                    Value::Map(vec![(
                        Value::Integer(oak_dice::cert::SHA2_256_ID.into()),
                        Value::Bytes(vec![0u8; 32]),
                    )]),
                ),
                (
                    Value::Integer(oak_dice::cert::FINAL_LAYER_CONFIG_MEASUREMENT_ID.into()),
                    Value::Map(vec![(
                        Value::Integer(oak_dice::cert::SHA2_256_ID.into()),
                        Value::Bytes(vec![0u8; 32]),
                    )]),
                ),
            ]),
        )];

        let system_public_key_id_hex =
            hex::encode(oak_dice::cert::derive_verifying_key_id(&system_public_key));
        let app_encryption_cert = oak_dice::cert::generate_kem_certificate(
            &system_private_key,
            system_public_key_id_hex.clone(),
            &app_encryption_public_key_bytes,
            container_claims.clone(),
        )
        .expect("failed to generate app encryption certificate");
        let app_signing_cert = oak_dice::cert::generate_signing_certificate(
            &system_private_key,
            system_public_key_id_hex,
            &app_signing_public_key,
            container_claims,
        )
        .expect("failed to generate app signing certificate");

        let application_keys = ApplicationKeys {
            encryption_public_key_certificate: app_encryption_cert
                .to_vec()
                .expect("failed to serialize app encryption certificate"),
            signing_public_key_certificate: app_signing_cert
                .to_vec()
                .expect("failed to serialize app signing certificate"),
            ..Default::default()
        };

        let layers = vec![
            LayerEvidence {
                eca_certificate: kernel_cert
                    .to_vec()
                    .expect("failed to serialize kernel certificate"),
            },
            LayerEvidence {
                eca_certificate: system_cert
                    .to_vec()
                    .expect("failed to serialize system certificate"),
            },
        ];

        let evidence = Evidence {
            root_layer: Some(root_layer),
            layers,
            application_keys: Some(application_keys),
            event_log: None,
            transparent_event_log: None,
        };

        // We return app_signing_private_key because it's the one signing the data
        (evidence, app_signing_private_key)
    }

    // Also see //oak_sev_snp_attestation_report.
    fn create_fake_attestation_report(root_public_key: CoseKey) -> Vec<u8> {
        let mut remote_attestation_report = vec![0u8; 1184];
        // report_data: offset 80 (0x50). Length 32.
        remote_attestation_report[80..80 + 32].copy_from_slice(&Sha256::digest(
            root_public_key.to_vec().expect("failed to serialize public key"),
        ));
        remote_attestation_report
    }

    fn empty_endorsements() -> Endorsements {
        Endorsements {
            r#type: Some(oak_proto_rust::oak::attestation::v1::endorsements::Type::OakContainers(
                OakContainersEndorsements {
                    root_layer: Some(RootLayerEndorsements::default()),
                    ..Default::default()
                },
            )),
            ..Default::default()
        }
    }

    fn insecure_reference_values() -> ReferenceValues {
        ReferenceValues {
            r#type: Some(reference_values::Type::OakContainers(OakContainersReferenceValues {
                root_layer: Some(RootLayerReferenceValues {
                    insecure: Some(
                        oak_proto_rust::oak::attestation::v1::InsecureReferenceValues {},
                    ),
                    ..Default::default()
                }),
                kernel_layer: Some(KernelLayerReferenceValues {
                    kernel: Some(KernelBinaryReferenceValue {
                        r#type: Some(kernel_binary_reference_value::Type::Skip(
                            oak_proto_rust::oak::attestation::v1::SkipVerification {},
                        )),
                    }),
                    kernel_cmd_line_text: Some(TextReferenceValue {
                        r#type: Some(text_reference_value::Type::Skip(
                            oak_proto_rust::oak::attestation::v1::SkipVerification {},
                        )),
                    }),
                    init_ram_fs: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            oak_proto_rust::oak::attestation::v1::SkipVerification {},
                        )),
                    }),
                    memory_map: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            oak_proto_rust::oak::attestation::v1::SkipVerification {},
                        )),
                    }),
                    acpi: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            oak_proto_rust::oak::attestation::v1::SkipVerification {},
                        )),
                    }),
                }),
                system_layer: Some(SystemLayerReferenceValues {
                    system_image: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            oak_proto_rust::oak::attestation::v1::SkipVerification {},
                        )),
                    }),
                }),
                container_layer: Some(ContainerLayerReferenceValues {
                    binary: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            oak_proto_rust::oak::attestation::v1::SkipVerification {},
                        )),
                    }),
                    configuration: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            oak_proto_rust::oak::attestation::v1::SkipVerification {},
                        )),
                    }),
                }),
            })),
        }
    }
}
