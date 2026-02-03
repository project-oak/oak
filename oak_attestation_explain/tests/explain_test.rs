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
use oak_attestation_verification::extract_evidence;
use oak_proto_rust::oak::attestation::v1::{
    OakRestrictedKernelData, extracted_evidence::EvidenceValues,
};
use test_util::{
    attestation_data::AttestationData, create_reference_values_for_extracted_evidence,
};

#[test]
fn produces_expected_explanation() {
    let d = AttestationData::load_milan_rk_staging();
    let mut extracted_evidence = extract_evidence(&d.evidence).expect("could not extract evidence");
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
https://search.sigstore.dev/?hash=30fa578f7781cdffc9f5c52ecfab95fe09e067583660c32d17ef3d18f9f33d87

ⓘ The firmware attestation digest is the SHA2-256 hash of the SHA2-384 hash of the initial memory state taken by the AMD SoC. The original SHA2-384 hash of the initial memory is: SHA2-384:0a3c0fa3f1558a883660cb3f37491e6da05e3445dc0f517ab5f9b8f7be6dc2ae2fa46a23b501d66d1d7e24796d1c2e20; it is listed as the 'initial_measurement' in the evidence of this layer.

The evidence describing this layer is outlined below.

sev_snp:
  current_tcb:
    boot_loader: 4
    fmc: 0
    microcode: 219
    snp: 24
    tee: 0
  debug: false
  hardware_id: 6c65aee8a139e984657ee8bfe50cbdc39067e3a99da09bba4e948236c91df95baa7bbd233fa56b101b90d136c7a78091013a7ce62c31fc25be1c6ca87da31a5a
  initial_measurement: 0a3c0fa3f1558a883660cb3f37491e6da05e3445dc0f517ab5f9b8f7be6dc2ae2fa46a23b501d66d1d7e24796d1c2e20
  product: 1
  report_data: 3e25197771c57f52a65c7bc55aada68f667d3a85f8b3fb0c15493ce0ae4e68b60000000000000000000000000000000000000000000000000000000000000000
  reported_tcb:
    boot_loader: 4
    fmc: 0
    microcode: 219
    snp: 24
    tee: 0
  vmpl: 0
"
                    );
                    assert_eq!(
                        kernel_layer.description().unwrap(),
"Attestations identifying the binaries captured in the evidence in this layer can be found as outlined below.
Kernel: https://search.sigstore.dev/?hash=3e7c371858f2bd9c032894694bd5bb4893f2403ce8a0bcf73c07af3ef6a35a15
Initial Ramdisk: https://search.sigstore.dev/?hash=15fe687a68a1f0d8aff14611fd4d108d7c132e3f8072bb64ff1073fb816a9ae8

The evidence describing the kernel layer is outlined below.

acpi:
  sha2_256: 141f52e83b42331118ed7b2a0b8b1f1bbab304e01973c79ad4cf6e172612d9f8
init_ram_fs:
  sha2_256: 15fe687a68a1f0d8aff14611fd4d108d7c132e3f8072bb64ff1073fb816a9ae8
kernel_image:
  sha2_256: 3e7c371858f2bd9c032894694bd5bb4893f2403ce8a0bcf73c07af3ef6a35a15
kernel_raw_cmd_line: console=ttyS0
kernel_setup_data:
  sha2_256: 4cd020820da663063f4185ca14a7e803cd7c9ca1483c64e836db840604b6fac1
memory_map:
  sha2_256: 79ae6053b1afd95db05643d3676af49fa7ea30c5b3579d090be9a18ae7030308
"
                    );
                    assert_eq!(
                        application_layer.description().unwrap(),
                        "The evidence describing the application is outlined below.

binary:
  sha2_256: 41e322b8cabb0890f9100b58886fa28b0eba7c9514b5e73f292d2900fe4c9eae
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
    let d = AttestationData::load_milan_rk_staging();
    let extracted_evidence = extract_evidence(&d.evidence).expect("could not extract evidence");
    let reference_values = create_reference_values_for_extracted_evidence(extracted_evidence);

    assert_eq!(
        reference_values.description().expect("could not get reference values description"),
  "_____ Root Layer _____

The attestation must be rooted in an AMD SEV-SNP TEE.

Attestations identifying firmware artifacts accepted by the reference values for this layer can be found at:
- https://search.sigstore.dev/?hash=30fa578f7781cdffc9f5c52ecfab95fe09e067583660c32d17ef3d18f9f33d87

ⓘ In reference values for AMD SEV-SNP TEEs, the firmware is captured as a SHA2-384 hash. This is the expected memory measurement that would be taken by the TEE. Attestations that describe this firmware, reference it using the SHA2-256 hash of the SHA2-384 hash.

The reference values describing this layer are printed below.

amd_sev:
  allow_debug: false
  check_vcek_cert_expiry: true
  genoa:
    minimum:
      boot_loader: 4
      fmc: 0
      microcode: 219
      snp: 24
      tee: 0
  milan:
    minimum:
      boot_loader: 4
      fmc: 0
      microcode: 219
      snp: 24
      tee: 0
  min_tcb_version:
    boot_loader: 4
    fmc: 0
    microcode: 219
    snp: 24
    tee: 0
  stage0:
    digests:
    - sha2_384: 0a3c0fa3f1558a883660cb3f37491e6da05e3445dc0f517ab5f9b8f7be6dc2ae2fa46a23b501d66d1d7e24796d1c2e20
  turin:
    minimum:
      boot_loader: 4
      fmc: 0
      microcode: 219
      snp: 24
      tee: 0


_____ Kernel Layer _____

Attestations identifying artifacts accepted by the reference values for this layer are described below.

Accepted Kernel Image Artifacts:
- https://search.sigstore.dev/?hash=3e7c371858f2bd9c032894694bd5bb4893f2403ce8a0bcf73c07af3ef6a35a15
Accepted Initial Ramdisk Artifacts:
- https://search.sigstore.dev/?hash=15fe687a68a1f0d8aff14611fd4d108d7c132e3f8072bb64ff1073fb816a9ae8


The reference values describing this layer are printed below.

acpi:
  digests:
  - sha2_256: 141f52e83b42331118ed7b2a0b8b1f1bbab304e01973c79ad4cf6e172612d9f8
init_ram_fs:
  digests:
  - sha2_256: 15fe687a68a1f0d8aff14611fd4d108d7c132e3f8072bb64ff1073fb816a9ae8
kernel:
  digests:
    image:
    - sha2_256: 3e7c371858f2bd9c032894694bd5bb4893f2403ce8a0bcf73c07af3ef6a35a15
    setup_data:
    - sha2_256: 4cd020820da663063f4185ca14a7e803cd7c9ca1483c64e836db840604b6fac1
kernel_cmd_line_text:
  string_literals:
  - console=ttyS0
memory_map:
  digests:
  - sha2_256: 79ae6053b1afd95db05643d3676af49fa7ea30c5b3579d090be9a18ae7030308


_____ Application Layer _____

binary:
  digests:
  - sha2_256: 41e322b8cabb0890f9100b58886fa28b0eba7c9514b5e73f292d2900fe4c9eae
configuration:
  skip: {}
");
}
