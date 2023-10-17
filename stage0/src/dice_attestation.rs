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

use alloc::{string::String, vec, vec::Vec};
use coset::{cbor::value::Value, cwt::ClaimName, CoseError, CoseSign1};
use oak_dice::cert::{
    derive_public_key_id, generate_eca_certificate, generate_ecdsa_keys, ACPI_MEASUREMENT_ID,
    INITRD_MEASUREMENT_ID, KERNEL_COMMANDLINE_MEASUREMENT_ID, KERNEL_MEASUREMENT_ID,
    MEMORY_MAP_MEASUREMENT_ID, SETUP_DATA_MEASUREMENT_ID,
};
use p384::ecdsa::SigningKey;

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
) -> Result<(CoseSign1, SigningKey), CoseError> {
    // Generate additional claims to cover the measurements.

    let additional_claims = vec![
        (
            ClaimName::PrivateUse(KERNEL_MEASUREMENT_ID),
            Value::Bytes(Vec::from(measurements.kernel_measurement)),
        ),
        (
            ClaimName::PrivateUse(KERNEL_COMMANDLINE_MEASUREMENT_ID),
            Value::Bytes(Vec::from(measurements.cmdline_measurement)),
        ),
        (
            ClaimName::PrivateUse(SETUP_DATA_MEASUREMENT_ID),
            Value::Bytes(Vec::from(measurements.setup_data_measurement)),
        ),
        (
            ClaimName::PrivateUse(INITRD_MEASUREMENT_ID),
            Value::Bytes(Vec::from(measurements.ram_disk_measurement)),
        ),
        (
            ClaimName::PrivateUse(MEMORY_MAP_MEASUREMENT_ID),
            Value::Bytes(Vec::from(measurements.memory_map_measurement)),
        ),
        (
            ClaimName::PrivateUse(ACPI_MEASUREMENT_ID),
            Value::Bytes(Vec::from(measurements.acpi_measurement)),
        ),
    ];
    generate_eca_certificate(stage0_eca_key, stage0_cert_issuer, additional_claims)
}

/// Generates signed attestation for the 'measurements' of all Stage 1 components.
pub fn generate_stage1_attestation(measurements: &Measurements) {
    // Generate Stage0 keys. This key will be used to sign Stage1
    // measurement+config and the stage1_ca_key.
    let (stage0_eca_key, stage0_eca_verifying_key) = generate_ecdsa_keys();

    // Call generate_attestation_report() to get 'stage0_ca_verifying_key' added to attestation
    // report.
    log::debug!(
        "Stage0 Verification key: {}",
        hex::encode(stage0_eca_verifying_key.to_encoded_point(false).as_bytes())
    );

    // Generate Stage1 CWT.
    let stage1_eca = generate_stage1_certificate(
        &stage0_eca_key,
        hex::encode(derive_public_key_id(&stage0_eca_verifying_key)),
        measurements,
    );
    if stage1_eca.is_ok() {
        // Call code that transmits the following to Stage1.
        // 1. stage0_eca_verifying_key
        // 2. stage1_eca.0 (the Stage 1 evidence)
        // 3. stage1_eca.1 (the Stage 1 ECA private key)
        log::debug!("Signing was successful..");
        return;
    }
    log::debug!("Error in signing: {}", stage1_eca.unwrap_err())
}
