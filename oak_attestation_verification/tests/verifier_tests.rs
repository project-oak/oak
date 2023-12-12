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

use prost::Message;
use std::fs;

use oak_attestation_verification::{
    proto::oak::attestation::v1::{
        attestation_results::Status, AmdSevReferenceValues, BinaryReferenceValue,
        ContainerLayerEndorsements, ContainerLayerReferenceValues, EndorsementReferenceValue,
        Endorsements, Evidence, KernelLayerEndorsements, KernelLayerReferenceValues,
        OakContainersEndorsements, OakContainersReferenceValues, ReferenceValues,
        RootLayerEndorsements, RootLayerReferenceValues, StringReferenceValue,
        SystemLayerEndorsements, SystemLayerReferenceValues, TransparentReleaseEndorsement,
    },
    util::convert_pem_to_raw,
    verifier::verify,
};

const ENDORSEMENT_PATH: &str = "testdata/endorsement.json";
const SIGNATURE_PATH: &str = "testdata/endorsement.json.sig";
const LOG_ENTRY_PATH: &str = "testdata/logentry.json";
const ENDORSER_PUBLIC_KEY_PATH: &str = "testdata/oak-development.pem";
const REKOR_PUBLIC_KEY_PATH: &str = "testdata/rekor_public_key.pem";
const EVIDENCE_PATH: &str = "testdata/evidence.binarypb";

// Pretend the tests run at this time: 1 Nov 2023, 9:00 UTC
const NOW_UTC_MILLIS: i64 = 1698829200000;

// Creates a valid evidence instance.
fn create_evidence() -> Evidence {
    let serialized = fs::read(EVIDENCE_PATH).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Creates valid endorsements for an Oak Containers chain.
fn create_endorsements() -> Endorsements {
    let endorsement = fs::read(ENDORSEMENT_PATH).expect("couldn't read endorsement");
    let signature = fs::read(SIGNATURE_PATH).expect("couldn't read signature");
    let log_entry = fs::read(LOG_ENTRY_PATH).expect("couldn't read log entry");

    // Use this for all binaries.
    let tre = TransparentReleaseEndorsement {
        endorsement,
        endorsement_signature: signature,
        rekor_log_entry: log_entry,
    };

    let root_layer = RootLayerEndorsements {
        tee_certificate: b"T O D O".to_vec(),
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
        r#type: Some(oak_attestation_verification::proto::oak::attestation::v1::endorsements::Type::OakContainers(ends)),
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
    let brv = BinaryReferenceValue {
        r#type: Some(oak_attestation_verification::proto::oak::attestation::v1::binary_reference_value::Type::Endorsement(erv)),
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
        intel_tdx: None,
    };
    let kernel_layer = KernelLayerReferenceValues {
        kernel_image: Some(brv.clone()),
        kernel_cmd_line: Some(brv.clone()),
        kernel_setup_data: Some(brv.clone()),
        init_ram_fs: Some(brv.clone()),
        memory_map: Some(brv.clone()),
        acpi: Some(brv.clone()),
    };
    let system_layer = SystemLayerReferenceValues {
        system_image: Some(brv.clone()),
    };
    let container_layer = ContainerLayerReferenceValues {
        binary: Some(brv.clone()),
        configuration: Some(brv.clone()),
    };
    let vs = OakContainersReferenceValues {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        system_layer: Some(system_layer),
        container_layer: Some(container_layer),
    };
    ReferenceValues {
        r#type: Some(oak_attestation_verification::proto::oak::attestation::v1::reference_values::Type::OakContainers(vs)),
    }
}

#[test]
fn verify_succeeds() {
    let evidence = create_evidence();
    let endorsements = create_endorsements();
    let reference_values = create_reference_values();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);

    eprintln!("======================================");
    eprintln!("code={} reason={}", r.status as i32, r.reason);
    eprintln!("======================================");
    assert!(r.status() == Status::Success);
}

#[test]
fn verify_fails_with_manipulated_root_public_key() {
    let mut evidence = create_evidence();
    evidence.root_layer.as_mut().unwrap().eca_public_key[0] += 1;
    let endorsements = create_endorsements();
    let reference_values = create_reference_values();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);

    eprintln!("======================================");
    eprintln!("code={} reason={}", r.status as i32, r.reason);
    eprintln!("======================================");
    assert!(r.status() == Status::GenericFailure);
}

#[test]
fn verify_fails_with_empty_args() {
    let evidence = Evidence::default();
    let endorsements = Endorsements::default();
    let reference_values = ReferenceValues::default();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);

    assert!(r.status() == Status::GenericFailure);
}
