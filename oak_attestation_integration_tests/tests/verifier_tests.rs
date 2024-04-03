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
//

use oak_attestation::dice::evidence_to_proto;
use oak_attestation_verification::verifier::{to_attestation_results, verify, verify_dice_chain};
use oak_proto_rust::oak::attestation::v1::{
    attestation_results::Status, binary_reference_value, endorsements,
    kernel_binary_reference_value, reference_values, text_reference_value,
    ApplicationLayerReferenceValues, BinaryReferenceValue, Endorsements, InsecureReferenceValues,
    KernelBinaryReferenceValue, KernelLayerReferenceValues, OakRestrictedKernelEndorsements,
    OakRestrictedKernelReferenceValues, ReferenceValues, RootLayerEndorsements,
    RootLayerReferenceValues, SkipVerification, TextReferenceValue,
};
use oak_restricted_kernel_sdk::attestation::EvidenceProvider;

// Pretend the tests run at this time: 1 Nov 2023, 9:00 UTC
const NOW_UTC_MILLIS: i64 = 1698829200000;

#[test]
fn verify_mock_dice_chain() {
    let mock_evidence_provider = oak_restricted_kernel_sdk::testing::MockEvidenceProvider::create()
        .expect("failed to create mock provider");
    let mock_evidence = mock_evidence_provider.get_evidence();

    let result = verify_dice_chain(
        &evidence_to_proto(mock_evidence.clone()).expect("could not convert evidence to proto"),
    );

    assert!(result.is_ok());
    let evidence_values: oak_proto_rust::oak::attestation::v1::extracted_evidence::EvidenceValues =
        result.unwrap().evidence_values.unwrap();
    assert!(matches!(evidence_values, oak_proto_rust::oak::attestation::v1::extracted_evidence::EvidenceValues::OakRestrictedKernel{..}))
}

#[test]
fn verify_mock_evidence() {
    let mock_evidence_provider = oak_restricted_kernel_sdk::testing::MockEvidenceProvider::create()
        .expect("failed to create mock provider");
    let evidence = evidence_to_proto(mock_evidence_provider.get_evidence().clone())
        .expect("failed to convert evidence to proto");

    let endorsements = Endorsements {
        r#type: Some(endorsements::Type::OakRestrictedKernel(OakRestrictedKernelEndorsements {
            root_layer: Some(RootLayerEndorsements::default()),
            ..Default::default()
        })),
    };

    // reference values that skip everything.
    let reference_values = {
        let skip = BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Skip(SkipVerification::default())),
        };
        ReferenceValues {
            r#type: Some(reference_values::Type::OakRestrictedKernel(
                OakRestrictedKernelReferenceValues {
                    root_layer: Some(RootLayerReferenceValues {
                        insecure: Some(InsecureReferenceValues::default()),
                        ..Default::default()
                    }),
                    #[allow(deprecated)]
                    kernel_layer: Some(KernelLayerReferenceValues {
                        kernel: Some(KernelBinaryReferenceValue {
                            r#type: Some(kernel_binary_reference_value::Type::Skip(
                                SkipVerification {},
                            )),
                        }),
                        kernel_image: None,
                        kernel_setup_data: None,
                        kernel_cmd_line: None,
                        kernel_cmd_line_regex: None,
                        kernel_cmd_line_text: Some(TextReferenceValue {
                            r#type: Some(text_reference_value::Type::Skip(SkipVerification {})),
                        }),
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
