//
// Copyright 2023 The Project Oak Authors
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

use std::fs;

use oak_attestation::dice::evidence_to_proto;
use oak_attestation_verification::{
    util::convert_pem_to_raw,
    verifier::{to_attestation_results, verify, verify_dice_chain},
};
use oak_proto_rust::oak::attestation::v1::{
    attestation_results::Status, binary_reference_value, endorsements, reference_values,
    AmdSevReferenceValues, ApplicationLayerReferenceValues, BinaryReferenceValue,
    ContainerLayerEndorsements, ContainerLayerReferenceValues, EndorsementReferenceValue,
    Endorsements, Evidence, InsecureReferenceValues, KernelLayerEndorsements,
    KernelLayerReferenceValues, OakContainersEndorsements, OakContainersReferenceValues,
    OakRestrictedKernelEndorsements, OakRestrictedKernelReferenceValues, ReferenceValues,
    RootLayerEndorsements, RootLayerReferenceValues, SkipVerification, StringReferenceValue,
    SystemLayerEndorsements, SystemLayerReferenceValues, TransparentReleaseEndorsement,
};
use oak_restricted_kernel_sdk::EvidenceProvider;
use prost::Message;

const ENDORSEMENT_PATH: &str = "testdata/endorsement.json";
const SIGNATURE_PATH: &str = "testdata/endorsement.json.sig";
const LOG_ENTRY_PATH: &str = "testdata/logentry.json";
const VCEK_MILAN_CERT_DER: &str = "testdata/vcek_milan.der";
const ENDORSER_PUBLIC_KEY_PATH: &str = "testdata/oak-development.pem";
const REKOR_PUBLIC_KEY_PATH: &str = "testdata/rekor_public_key.pem";
const EVIDENCE_PATH: &str = "testdata/evidence.binarypb";
const FAKE_EVIDENCE_PATH: &str = "testdata/fake_evidence.binarypb";

// Pretend the tests run at this time: 1 Nov 2023, 9:00 UTC
const NOW_UTC_MILLIS: i64 = 1698829200000;

// Creates a valid AMD SEV-SNP evidence instance.
fn create_evidence() -> Evidence {
    let serialized = fs::read(EVIDENCE_PATH).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Creates a valid fake evidence instance.
fn create_fake_evidence() -> Evidence {
    let serialized = fs::read(FAKE_EVIDENCE_PATH).expect("could not read fake evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode fake evidence")
}

// Creates valid endorsements for an Oak Containers chain.
fn create_endorsements() -> Endorsements {
    let endorsement = fs::read(ENDORSEMENT_PATH).expect("couldn't read endorsement");
    let signature = fs::read(SIGNATURE_PATH).expect("couldn't read signature");
    let log_entry = fs::read(LOG_ENTRY_PATH).expect("couldn't read log entry");
    let vcek_milan_cert = fs::read(VCEK_MILAN_CERT_DER).expect("couldn't read TEE cert");

    // Use this for all binaries.
    let tre = TransparentReleaseEndorsement {
        endorsement,
        endorsement_signature: signature,
        rekor_log_entry: log_entry,
    };

    let root_layer = RootLayerEndorsements {
        tee_certificate: vcek_milan_cert,
        stage0: Some(tre.clone()),
    };
    let kernel_layer = KernelLayerEndorsements {
        kernel_image: Some(tre.clone()),
        kernel_cmd_line: Some(tre.clone()),
        kernel_setup_data: Some(tre.clone()),
        init_ram_fs: Some(tre.clone()),
        memory_map: Some(tre.clone()),
        acpi: Some(tre.clone()),
    };
    let system_layer = SystemLayerEndorsements {
        system_image: Some(tre.clone()),
    };
    let container_layer = ContainerLayerEndorsements {
        binary: Some(tre.clone()),
        configuration: Some(tre.clone()),
    };

    let ends = OakContainersEndorsements {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        system_layer: Some(system_layer),
        container_layer: Some(container_layer),
    };
    Endorsements {
        r#type: Some(oak_proto_rust::oak::attestation::v1::endorsements::Type::OakContainers(ends)),
    }
}

// Creates valid reference values for an Oak Containers chain.
fn create_reference_values() -> ReferenceValues {
    let endorser_public_key_pem =
        fs::read_to_string(ENDORSER_PUBLIC_KEY_PATH).expect("couldn't read endorser public key");
    let rekor_public_key_pem =
        fs::read_to_string(REKOR_PUBLIC_KEY_PATH).expect("couldn't read rekor public key");

    let endorser_public_key = convert_pem_to_raw(endorser_public_key_pem.as_str())
        .expect("failed to convert endorser key");
    let rekor_public_key =
        convert_pem_to_raw(&rekor_public_key_pem).expect("failed to convert Rekor key");

    let erv = EndorsementReferenceValue {
        endorser_public_key,
        rekor_public_key,
    };
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };
    let brv = BinaryReferenceValue {
        r#type: Some(
            oak_proto_rust::oak::attestation::v1::binary_reference_value::Type::Endorsement(erv),
        ),
    };
    let srv = StringReferenceValue {
        values: ["whatever".to_owned()].to_vec(),
    };

    let amd_sev = AmdSevReferenceValues {
        amd_root_public_key: b"".to_vec(),
        firmware_version: Some(srv.clone()),
        allow_debug: false,
        stage0: Some(brv.clone()),
    };

    let root_layer = RootLayerReferenceValues {
        amd_sev: Some(amd_sev),
        ..Default::default()
    };
    let kernel_layer = KernelLayerReferenceValues {
        kernel_image: Some(skip.clone()),
        kernel_cmd_line: Some(skip.clone()),
        kernel_setup_data: Some(skip.clone()),
        init_ram_fs: Some(skip.clone()),
        memory_map: Some(skip.clone()),
        acpi: Some(skip.clone()),
    };
    let system_layer = SystemLayerReferenceValues {
        system_image: Some(skip.clone()),
    };
    let container_layer = ContainerLayerReferenceValues {
        binary: Some(skip.clone()),
        configuration: Some(skip.clone()),
    };
    let vs = OakContainersReferenceValues {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        system_layer: Some(system_layer),
        container_layer: Some(container_layer),
    };
    ReferenceValues {
        r#type: Some(reference_values::Type::OakContainers(vs)),
    }
}

#[test]
fn verify_succeeds() {
    let evidence = create_evidence();
    let endorsements = create_endorsements();
    let reference_values = create_reference_values();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_mock_dice_chain() {
    let mock_evidence_provider =
        oak_restricted_kernel_sdk::mock_attestation::MockEvidenceProvider::create()
            .expect("failed to create mock provider");
    let mock_evidence = mock_evidence_provider.get_evidence();

    let result = verify_dice_chain(
        &evidence_to_proto(mock_evidence.clone()).expect("could not convert evidence to proto"),
    );

    assert!(result.is_ok())
}

#[test]
fn verify_mock_evidence() {
    let mock_evidence_provider =
        oak_restricted_kernel_sdk::mock_attestation::MockEvidenceProvider::create()
            .expect("failed to create mock provider");
    let evidence = evidence_to_proto(mock_evidence_provider.get_evidence().clone())
        .expect("failed to convert evidence to proto");

    let endorsements = Endorsements {
        r#type: Some(endorsements::Type::OakRestrictedKernel(
            OakRestrictedKernelEndorsements {
                root_layer: Some(RootLayerEndorsements::default()),
                ..Default::default()
            },
        )),
    };

    // reference values that skip everything.
    let reference_values = {
        let skip = BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Skip(
                SkipVerification::default(),
            )),
        };
        ReferenceValues {
            r#type: Some(reference_values::Type::OakRestrictedKernel(
                OakRestrictedKernelReferenceValues {
                    root_layer: Some(RootLayerReferenceValues {
                        insecure: Some(InsecureReferenceValues::default()),
                        ..Default::default()
                    }),
                    kernel_layer: Some(KernelLayerReferenceValues {
                        kernel_image: Some(skip.clone()),
                        kernel_cmd_line: Some(skip.clone()),
                        kernel_setup_data: Some(skip.clone()),
                        init_ram_fs: Some(skip.clone()),
                        memory_map: Some(skip.clone()),
                        acpi: Some(skip.clone()),
                    }),
                    application_layer: Some(ApplicationLayerReferenceValues {
                        binary: Some(skip.clone()),
                        configuration: Some(skip.clone()),
                    }),
                },
            )),
        }
    };

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_fake_evidence() {
    let evidence = create_fake_evidence();
    let endorsements = create_endorsements();
    let mut reference_values = create_reference_values();
    if let Some(reference_values::Type::OakContainers(reference)) = reference_values.r#type.as_mut()
    {
        reference.root_layer = Some(RootLayerReferenceValues {
            insecure: Some(InsecureReferenceValues {}),
            ..Default::default()
        });
    } else {
        panic!("invalid reference value type");
    }

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_fails_with_manipulated_root_public_key() {
    let mut evidence = create_evidence();
    evidence.root_layer.as_mut().unwrap().eca_public_key[0] += 1;
    let endorsements = create_endorsements();
    let reference_values = create_reference_values();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_err());
    assert!(p.status() == Status::GenericFailure);
}

#[test]
fn verify_fails_with_empty_args() {
    let evidence = Evidence::default();
    let endorsements = Endorsements::default();
    let reference_values = ReferenceValues::default();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    assert!(r.is_err());
    assert!(p.status() == Status::GenericFailure);
}
