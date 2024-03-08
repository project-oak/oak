//
// Copyright 2024 The Project Oak Authors
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

use std::fs;

use oak_attestation_verification::verifier::{to_attestation_results, verify};
use oak_proto_rust::oak::attestation::v1::{
    attestation_results::Status, binary_reference_value, reference_values, AmdSevReferenceValues,
    ApplicationLayerReferenceValues, BinaryReferenceValue, Endorsements, Evidence,
    KernelLayerReferenceValues, OakRestrictedKernelReferenceValues, ReferenceValues,
    RootLayerReferenceValues, SkipVerification,
};
use prost::Message;

// Timestamp taken for the purpose of demo: 5 Mar 2024, 12:27 UTC.
const NOW_UTC_MILLIS: i64 = 1709641620000;
const EVIDENCE_PATH: &str = "demo_oc3_2024/testdata/evidence.binarypb";
const ENDORSEMENTS_PATH: &str = "demo_oc3_2024/testdata/endorsements.binarypb";

fn create_reference_values() -> ReferenceValues {
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(
            SkipVerification::default(),
        )),
    };

    let amd_sev = AmdSevReferenceValues {
        amd_root_public_key: b"".to_vec(),
        firmware_version: None,
        allow_debug: false,
        // See b/327069120: Do not skip over stage0.
        stage0: Some(skip.clone()),
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
    let application_layer = ApplicationLayerReferenceValues {
        binary: Some(skip.clone()),
        configuration: Some(skip.clone()),
    };

    let reference_values = OakRestrictedKernelReferenceValues {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        application_layer: Some(application_layer),
    };
    ReferenceValues {
        r#type: Some(reference_values::Type::OakRestrictedKernel(
            reference_values,
        )),
    }
}

fn main() {
    let serialized_evidence = fs::read(EVIDENCE_PATH).expect("couldn't read evidence");
    let evidence =
        Evidence::decode(serialized_evidence.as_slice()).expect("couldn't decode evidence");

    let serialized_endorsements = fs::read(ENDORSEMENTS_PATH).expect("couldn't read endorsements");
    let endorsements = Endorsements::decode(serialized_endorsements.as_slice())
        .expect("couldn't decode endorsements");

    let reference_values = create_reference_values();

    let attestation_results = to_attestation_results(&verify(
        NOW_UTC_MILLIS,
        &evidence,
        &endorsements,
        &reference_values,
    ));

    match attestation_results.status() {
        Status::Success => println!("Verification successful"),
        Status::GenericFailure => {
            eprintln!(
                "Couldn't verify endorsed evidence: code={} reason={}",
                attestation_results.status as i32, attestation_results.reason
            );
        }
        Status::Unspecified => eprintln!("Illegal status code in attestation results"),
    }
}
