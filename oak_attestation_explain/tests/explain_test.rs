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
#![feature(assert_matches)]

use std::fs;

use oak_attestation_explain::{HumanReadableExplanation, HumanReadableTitle};
use oak_proto_rust::oak::attestation::v1::{
    extracted_evidence::EvidenceValues, Evidence, OakRestrictedKernelData,
};
use prost::Message;

// TODO: b/334900893 - Generate extracted evidence programatically.
const RK_EVIDENCE_PATH: &str = "testdata/rk_evidence.binarypb";

#[test]
fn produces_expected_explaination() {
    let mut extracted_evidence = {
        let serialized = fs::read(RK_EVIDENCE_PATH).expect("could not read extracted evidence");
        let evidence = Evidence::decode(serialized.as_slice()).expect("could not decode evidence");
        oak_attestation_verification::verifier::extract_evidence(&evidence)
            .expect("could not extract evidence")
    };

    eprintln!("{:?}", extracted_evidence.evidence_values);
    match extracted_evidence.evidence_values.take() {
        Some(EvidenceValues::OakRestrictedKernel(restricted_kernel_evidence)) => {
            assert_eq!(
                restricted_kernel_evidence.title().unwrap(),
                format!("Oak Restricted Kernel Stack in a {} TEE", "AMD SEV-SNP")
            );
            match restricted_kernel_evidence {
                OakRestrictedKernelData {
                    root_layer: Some(root_layer),
                    kernel_layer: Some(kernel_layer),
                    application_layer: Some(application_layer),
                } => {
                    assert_eq!(
                        root_layer.description().unwrap(),
                        r#"Firmware [Digest]: SHA2-256:33d5453b09e16ed0d6deb7c9f076b66b92a1b472d89534034717143554f6746d
ⓘ The firmware attestation digest is the SHA2-256 hash of the SHA2-384 hash of the initial memory state taken by the AMD SoC. The original SHA2-384 hash of the initial memory is: SHA2-384:6c090e4594fd40ee186c90d43f7ad8d904838baa9643a4be1d9d4ff0fdd670a62565e2417660008e058cc2f2029eac8a.
Firmware [Provenances]: https://search.sigstore.dev/?hash=33d5453b09e16ed0d6deb7c9f076b66b92a1b472d89534034717143554f6746d"#
                    );
                    assert_eq!(
                        kernel_layer.description().unwrap(),
                        r#"Kernel Image [Digest]: SHA2-256:ec752c660481432f525f49d0be1521c7ea42ebbf2ce705aad2781a329e1001d8
Kernel Setup Data [Digest]: SHA2-256:4cd020820da663063f4185ca14a7e803cd7c9ca1483c64e836db840604b6fac1
Kernel Image/Setup-Data [Provenances]: https://search.sigstore.dev/?hash=ec752c660481432f525f49d0be1521c7ea42ebbf2ce705aad2781a329e1001d8
Kernel Command Line [String]: console=ttyS0
Initial RAM Disk [Digest]: SHA2-256:daf79f24b5744340ac18c2b468e7e0a7915684c5dfda2450acfa7225bdc75bb8
Inital RAM Disk [Provenances]: https://search.sigstore.dev/?hash=daf79f24b5744340ac18c2b468e7e0a7915684c5dfda2450acfa7225bdc75bb8"#
                    );
                    assert_eq!(
                        application_layer.description().unwrap(),
                        r#"Binary [Digest]: SHA2-256:7d4682a9a0f97ade0fad9a47f247e1cb6ed326e80ba05ea39fc84b2fe6bcacfb
Binary [Provenances]: https://search.sigstore.dev/?hash=7d4682a9a0f97ade0fad9a47f247e1cb6ed326e80ba05ea39fc84b2fe6bcacfb"#
                    );
                }
                _ => panic!("evidence values unexpectedly unset"),
            }
        }
        _ => panic!("not restricted kernel evidence"),
    }
}
