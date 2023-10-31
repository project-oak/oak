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

use alloc::{boxed::Box, string::String, vec, vec::Vec};
use coset::{cbor::value::Value, cwt::ClaimName, CborSerializable, CoseSign1};
use oak_dice::{
    cert::{
        derive_public_key_id, generate_eca_certificate, generate_ecdsa_key_pair,
        public_key_to_cose_key, ACPI_MEASUREMENT_ID, INITRD_MEASUREMENT_ID,
        KERNEL_COMMANDLINE_MEASUREMENT_ID, KERNEL_MEASUREMENT_ID, MEMORY_MAP_MEASUREMENT_ID,
        SETUP_DATA_MEASUREMENT_ID,
    },
    evidence::{Stage0DiceData, TeePlatform, STAGE0_MAGIC},
};
use oak_sev_guest::guest::AttestationReport;
use p256::ecdsa::SigningKey;
use zerocopy::{AsBytes, FromZeroes};

// The number of custom bytes that can be included in the attestation report.
const REPORT_DATA_SIZE: usize = 64;

/// Measurements of various components in Stage1.
pub struct Measurements {
    /// The measurement of the kernel image.
    pub kernel_measurement: [u8; 32],
    /// The measurement of the kernel command-line.
    pub cmdline_measurement: [u8; 32],
    /// The measurement of the kernel setup data.
    pub setup_data_measurement: [u8; 32],
    /// The measurement of the initial RAM disk.
    pub ram_disk_measurement: [u8; 32],
    /// The measurement of the physical memory map.
    pub memory_map_measurement: [u8; 32],
    /// The concatenated measurement of the command used for building the ACPI tables.
    pub acpi_measurement: [u8; 32],
}

/// Generates an ECA certificate for use by the next boot stage (Stage 1).
fn generate_stage1_certificate(
    stage0_eca_key: &SigningKey,
    stage0_cert_issuer: String,
    measurements: &Measurements,
) -> (CoseSign1, SigningKey) {
    // Generate additional claims to cover the measurements.

    let additional_claims = vec![
        (
            ClaimName::PrivateUse(KERNEL_MEASUREMENT_ID),
            Value::Bytes(measurements.kernel_measurement.into()),
        ),
        (
            ClaimName::PrivateUse(KERNEL_COMMANDLINE_MEASUREMENT_ID),
            Value::Bytes(measurements.cmdline_measurement.into()),
        ),
        (
            ClaimName::PrivateUse(SETUP_DATA_MEASUREMENT_ID),
            Value::Bytes(measurements.setup_data_measurement.into()),
        ),
        (
            ClaimName::PrivateUse(INITRD_MEASUREMENT_ID),
            Value::Bytes(measurements.ram_disk_measurement.into()),
        ),
        (
            ClaimName::PrivateUse(MEMORY_MAP_MEASUREMENT_ID),
            Value::Bytes(measurements.memory_map_measurement.into()),
        ),
        (
            ClaimName::PrivateUse(ACPI_MEASUREMENT_ID),
            Value::Bytes(measurements.acpi_measurement.into()),
        ),
    ];
    generate_eca_certificate(stage0_eca_key, stage0_cert_issuer, additional_claims)
        .expect("couldn't generate ECA certificate")
}

/// Generates attestation evidence for the 'measurements' of all Stage 1 components.
pub fn generate_dice_data(measurements: &Measurements) -> &'static Stage0DiceData {
    let result = Box::leak(Box::new_in(
        Stage0DiceData::new_zeroed(),
        &crate::BOOT_ALLOC,
    ));

    // Generate ECA Stage0 key pair. This key will be used to sign Stage1 ECA certificate.
    let (stage0_eca_key, stage0_eca_verifying_key) = generate_ecdsa_key_pair();

    let (stage1_eca_cert, stage1_eca_signing_key) = generate_stage1_certificate(
        &stage0_eca_key,
        hex::encode(derive_public_key_id(&stage0_eca_verifying_key)),
        measurements,
    );

    let stage0_eca_verifying_key = public_key_to_cose_key(&stage0_eca_verifying_key)
        .to_vec()
        .expect("couldn't serialize the ECA public key");

    let stage1_eca_cert = stage1_eca_cert
        .to_vec()
        .expect("couldn't serialize stage 1 ECA certificate");

    let stage1_eca_signing_key: Vec<u8> = stage1_eca_signing_key.to_bytes().as_slice().into();

    // Use the SHA2-256 digest of the serialized ECA verifying key as the report data.
    let eca_measurement = crate::measure_byte_slice(&stage0_eca_verifying_key);
    let mut report_data = [0u8; REPORT_DATA_SIZE];
    report_data[..eca_measurement.len()].copy_from_slice(&eca_measurement[..]);

    let report = get_attestation(report_data).expect("couldn't get attestation report.");
    let report_bytes = report.as_bytes();

    result.magic = STAGE0_MAGIC;
    result.root_layer_evidence.tee_platform = TeePlatform::AmdSevSnp as u64;
    result.root_layer_evidence.remote_attestation_report[..report_bytes.len()]
        .copy_from_slice(report_bytes);
    result.root_layer_evidence.eca_public_key[..stage0_eca_verifying_key.len()]
        .copy_from_slice(&stage0_eca_verifying_key);
    result.layer_1_evidence.eca_certificate[..stage1_eca_cert.len()]
        .copy_from_slice(&stage1_eca_cert);
    result.layer_1_certificate_authority.eca_private_key[..stage1_eca_signing_key.len()]
        .copy_from_slice(&stage1_eca_signing_key);
    result
}

/// Returns an attestation report.
///
/// # Arguments
///
/// * `report_data` - The custom data that must be included in the report. This is typically used to
///   bind information (such as the hash of a public key) to the report.
pub fn get_attestation(
    report_data: [u8; REPORT_DATA_SIZE],
) -> Result<AttestationReport, &'static str> {
    // For now we just generate a fake report and set the report data.
    let mut report = AttestationReport::new_zeroed();
    report.data.report_data = report_data;
    Ok(report)
}
