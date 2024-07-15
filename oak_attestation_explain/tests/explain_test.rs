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

use oak_attestation_explain::{HumanReadableExplanation, HumanReadableTitle};
use oak_attestation_verification_test_utils::reference_values_from_evidence;
use oak_proto_rust::oak::attestation::v1::{
    extracted_evidence::EvidenceValues, Evidence, OakRestrictedKernelData, ReferenceValues,
};
use prost::Message;

const RK_EVIDENCE: &[u8] = include_bytes!("../testdata/rk_evidence.binarypb").as_slice();

#[test]
fn produces_expected_explaination() {
    let mut extracted_evidence = {
        // TODO: b/334900893 - Generate extracted evidence programatically.
        let evidence = Evidence::decode(RK_EVIDENCE).expect("could not decode evidence");
        oak_attestation_verification::verifier::extract_evidence(&evidence)
            .expect("could not extract evidence")
    };
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
                        "The attestation is rooted in an AMD SEV-SNP TEE.

Attestations identifying the firmware captured in the evidence can be found here:
https://search.sigstore.dev/?hash=33d5453b09e16ed0d6deb7c9f076b66b92a1b472d89534034717143554f6746d

ⓘ The firmware attestation digest is the SHA2-256 hash of the SHA2-384 hash of the initial memory state taken by the AMD SoC. The original SHA2-384 hash of the initial memory is: SHA2-384:6c090e4594fd40ee186c90d43f7ad8d904838baa9643a4be1d9d4ff0fdd670a62565e2417660008e058cc2f2029eac8a; it is listed as the 'initial_measurement' in the evidence of this layer.

The evidence describing this layer is outlined below.

sev_snp:
  current_tcb:
    boot_loader: 3
    microcode: 209
    snp: 20
    tee: 0
  debug: false
  hardware_id: 42e1f92660cc2bf7d996a4db5ebeafe83361eac6f96db350a70c7e07115fad60a85f5ae98b8fb87ec76ce2a3f81ad70df8aebbde1c3c21797897a04b616235ef
  initial_measurement: 6c090e4594fd40ee186c90d43f7ad8d904838baa9643a4be1d9d4ff0fdd670a62565e2417660008e058cc2f2029eac8a
  report_data: 8fc67415b81201f189f2d19cbe57aa66f7282916b5b9e6cca83ab8688f4499d30000000000000000000000000000000000000000000000000000000000000000
  reported_tcb:
    boot_loader: 3
    microcode: 209
    snp: 20
    tee: 0
  vmpl: 0
"
                    );
                    assert_eq!(
                        kernel_layer.description().unwrap(),
"Attestations identifying the binaries captured in the evidence in this layer can be found as outlined below.
Kernel: https://search.sigstore.dev/?hash=ec752c660481432f525f49d0be1521c7ea42ebbf2ce705aad2781a329e1001d8
Initial Ramdisk: https://search.sigstore.dev/?hash=daf79f24b5744340ac18c2b468e7e0a7915684c5dfda2450acfa7225bdc75bb8

The evidence describing the kernel layer is outlined below.

acpi:
  sha2_256: 64f555327287a2141476681e4e4dd80d5f75ab9c276f6db8effc55236dba9953
init_ram_fs:
  sha2_256: daf79f24b5744340ac18c2b468e7e0a7915684c5dfda2450acfa7225bdc75bb8
kernel_cmd_line:
  sha2_256: 2b98586d9905a605c295d77c61e8cfd2027ae5b8a04eefa9018436f6ad114297
kernel_image:
  sha2_256: ec752c660481432f525f49d0be1521c7ea42ebbf2ce705aad2781a329e1001d8
kernel_raw_cmd_line: console=ttyS0
kernel_setup_data:
  sha2_256: 4cd020820da663063f4185ca14a7e803cd7c9ca1483c64e836db840604b6fac1
memory_map:
  sha2_256: 1a7d55e1f4b3d13b5f537b2b50fd5cd8e94fddcde80b15524ab935289c2e3a08
"
                    );
                    assert_eq!(
                        application_layer.description().unwrap(),
                        "The evidence describing the application is outlined below.

binary:
  sha2_256: 7d4682a9a0f97ade0fad9a47f247e1cb6ed326e80ba05ea39fc84b2fe6bcacfb
config: {}
"
                    );
                }
                _ => panic!("evidence values unexpectedly unset"),
            }
        }
        _ => panic!("not restricted kernel evidence"),
    }
}

#[test]
fn produces_expected_reference_values_explaination() {
    let reference_values: ReferenceValues = {
        let extracted_evidence = {
            let evidence = Evidence::decode(RK_EVIDENCE).expect("could not decode evidence");
            oak_attestation_verification::verifier::extract_evidence(&evidence)
                .expect("could not extract evidence")
        };
        reference_values_from_evidence(extracted_evidence)
    };

    assert_eq!(
        reference_values.description().expect("could not get reference values description"),
"_____ Root Layer _____

The attestation must be rooted in an AMD SEV-SNP TEE.

Attestations identifying firmware artifacts accepted by the reference values for this layer can be found at:
- https://search.sigstore.dev/?hash=33d5453b09e16ed0d6deb7c9f076b66b92a1b472d89534034717143554f6746d

ⓘ In reference values for AMD SEV-SNP TEEs, the firmware is captured as a SHA2-384 hash. This is the expected memory measurement that would be taken by the TEE. Attestations that describe this firmware, reference it using the SHA2-256 hash of the SHA2-384 hash.

The reference values describing this layer are printed below.

amd_sev:
  allow_debug: false
  min_tcb_version:
    boot_loader: 3
    microcode: 209
    snp: 20
    tee: 0
  stage0:
    digests:
    - sha2_384: 6c090e4594fd40ee186c90d43f7ad8d904838baa9643a4be1d9d4ff0fdd670a62565e2417660008e058cc2f2029eac8a


_____ Kernel Layer _____

Attestations identifying artifacts accepted by the reference values for this layer are described below.

Accepted Kernel Image Artifacts:
- https://search.sigstore.dev/?hash=ec752c660481432f525f49d0be1521c7ea42ebbf2ce705aad2781a329e1001d8
Accepted Initial Ramdisk Artifacts:
- https://search.sigstore.dev/?hash=daf79f24b5744340ac18c2b468e7e0a7915684c5dfda2450acfa7225bdc75bb8


The reference values describing this layer are printed below.

acpi:
  digests:
  - sha2_256: 64f555327287a2141476681e4e4dd80d5f75ab9c276f6db8effc55236dba9953
init_ram_fs:
  digests:
  - sha2_256: daf79f24b5744340ac18c2b468e7e0a7915684c5dfda2450acfa7225bdc75bb8
kernel:
  digests:
    image:
    - sha2_256: ec752c660481432f525f49d0be1521c7ea42ebbf2ce705aad2781a329e1001d8
    setup_data:
    - sha2_256: 4cd020820da663063f4185ca14a7e803cd7c9ca1483c64e836db840604b6fac1
kernel_cmd_line_text:
  string_literals:
  - console=ttyS0
memory_map:
  digests:
  - sha2_256: 1a7d55e1f4b3d13b5f537b2b50fd5cd8e94fddcde80b15524ab935289c2e3a08


_____ Application Layer _____

binary:
  digests:
  - sha2_256: 7d4682a9a0f97ade0fad9a47f247e1cb6ed326e80ba05ea39fc84b2fe6bcacfb
configuration:
  skip: {}
"
    );
}
