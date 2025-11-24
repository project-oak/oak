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

use std::{
    convert::Infallible,
    path::{Path, PathBuf},
};

use clap::Parser;
use log::{error, info};
use oak_attestation_verification::verifier::verify;
use oak_proto_rust::oak::attestation::v1::{
    binary_reference_value, kernel_binary_reference_value, reference_values,
    tcb_version_reference_value, text_reference_value, AmdSevReferenceValues, BinaryReferenceValue,
    ContainerLayerReferenceValues, Digests, Endorsements, KernelBinaryReferenceValue,
    KernelDigests, KernelLayerReferenceValues, OakContainersReferenceValues, ReferenceValues,
    RootLayerReferenceValues, StringLiterals, SystemLayerReferenceValues, TcbVersion,
    TcbVersionReferenceValue, TextReferenceValue,
};
use p256::{
    ecdsa,
    ecdsa::{signature::Verifier, Signature, VerifyingKey},
};
use prost::Message;
use sha2::{Digest, Sha256};
use tonic_service::oak::ctf_sha2::containers::ArbiterInput;
use x509_cert::{der::Decode, Certificate};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long, value_parser = path_parser)]
    vcek_cert: PathBuf,

    #[clap(flatten)]
    pub falsify_args: falsify::FalsifyArgs,
}

fn path_parser(arg_value: &str) -> Result<PathBuf, Infallible> {
    // https://bazel.build/docs/user-manual#running-executables
    Ok(Path::new(&std::env::var("BUILD_WORKING_DIRECTORY").unwrap_or_default()).join(arg_value))
}

fn main() -> anyhow::Result<()> {
    env_logger::init();

    let Args { vcek_cert, falsify_args } = Args::parse();

    let vcek_cert = std::fs::read(vcek_cert)?;
    let vcek_cert_not_before = Certificate::from_der(vcek_cert.as_slice())
        .map_err(|e| anyhow::anyhow!("failed to parse VCEK certificate: {e}"))?
        .tbs_certificate
        .validity
        .not_before;

    let reference_values = create_reference_values();
    let endorsements = create_endorsements(vcek_cert.clone());

    falsify::falsify(falsify_args, |input_data| {
        let input = match ArbiterInput::decode(input_data.as_slice()) {
            Ok(input) => input,
            Err(e) => {
                error!("Input failed to decode: {e}");
                return;
            }
        };

        let response = match input.response {
            Some(response) => response,
            None => {
                error!("Input does not contain an enclave response message");
                return;
            }
        };

        // 1. Check flag digest
        let mut hasher = Sha256::new();
        hasher.update(&input.flag);
        let computed_digest = hasher.finalize();
        if computed_digest.as_slice() != response.flag_digest {
            info!(
                "Provided flag {} is incorrect: wanted digest {} but got {}",
                hex::encode(&input.flag),
                hex::encode(&response.flag_digest),
                hex::encode(computed_digest)
            );
            return;
        }

        // 2. Verify Evidence
        let evidence = match response.evidence {
            Some(evidence) => evidence,
            None => {
                error!("Input does not contain enclave evidence");
                return;
            }
        };

        let extracted = match verify(
            // Here we trust the VCEK "not before" timestamp. This is a bit circular, but there
            // is no obvious better alternative which results in deterministic behaviour.
            vcek_cert_not_before.to_unix_duration().as_millis() as i64,
            &evidence,
            &endorsements,
            &reference_values,
        ) {
            Ok(extracted) => extracted,
            Err(e) => {
                info!("Enclave evidence verification failed: {e:#}");
                return;
            }
        };

        // 3. Verify signature over flag digest
        assert!(
            verify_signature(
                &extracted.signing_public_key,
                &response.flag_digest,
                &response.signature,
            )
            .is_err(),
            "Signature verification succeeded! Claim falsified."
        );
    });
    Ok(())
}

fn verify_signature(
    public_key: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<(), ecdsa::Error> {
    VerifyingKey::from_sec1_bytes(public_key)?.verify(message, &Signature::from_slice(signature)?)
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

fn create_endorsements(vcek_cert: Vec<u8>) -> Endorsements {
    Endorsements {
        r#type: Some(oak_proto_rust::oak::attestation::v1::endorsements::Type::OakContainers(
            oak_proto_rust::oak::attestation::v1::OakContainersEndorsements {
                root_layer: Some(oak_proto_rust::oak::attestation::v1::RootLayerEndorsements {
                    tee_certificate: vcek_cert,
                    ..Default::default()
                }),
                ..Default::default()
            },
        )),
        ..Default::default()
    }
}
