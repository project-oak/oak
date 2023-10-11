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

extern crate alloc;

use alloc::{string::String, vec, vec::Vec};
use coset::{
    cbor::value::Value, cwt, iana, Algorithm, CborSerializable, CoseError, CoseKey, KeyOperation,
    KeyType, Label,
};
use hkdf::Hkdf;
use p384::ecdsa::{signature::Signer, Signature, SigningKey, VerifyingKey};
use rand_core::OsRng;
use sha2::Sha256;

/// String to be used as salt for generating Key IDs.
pub const ID_SALT: &str = "DICE_ID_SALT";
/// ID for the CWT private claim corresponding to the Subject of the CWT.
pub const SUBJECT_PUBLIC_KEY_ID: i64 = -4670552;
/// ID for bitstring used to describe the intended usage for the key represented by the certificate.
pub const KEY_USAGE_ID: i64 = -4670553;
/// ID for the CWT private claim corresponding to the VM kernel measurement.
pub const KERNEL_MEASUREMENT_ID: i64 = -4670555;
/// ID for the CWT private claim corresponding to the VM kernel commandline measurement.
pub const KERNEL_COMMANDLINE_MEASUREMENT_ID: i64 = -4670556;
/// ID for the CWT private claim corresponding to the VM kernel setup data measurement.
pub const SETUP_DATA_MEASUREMENT_ID: i64 = -4670557;
/// ID for the CWT private claim corresponding to the initial ramdisk measurement.
pub const INITRD_MEASUREMENT_ID: i64 = -4670558;
/// ID for the CWT private claim corresponding to the physical memory map (e820 table).
pub const MEMORY_MAP_MEASUREMENT_ID: i64 = -4670559;
/// ID for the CWT private claim corresponding to the hash of the commands for building the ACPI
/// tables.
pub const ACPI_MEASUREMENT_ID: i64 = -4670560;
/// Length of the unique ID for ECDSA keys generated.
pub const KEY_ID_LENGTH: usize = 20;
/// Info string for HKDF generator.
pub const INFO_STR: &str = "ID";

/// Attestation related functions.
///
/// Returns Signed Stage1 key and measurments.
struct Stage0Signer {
    signing_key: SigningKey,
}
/// Measurements of various components in Stage1.
pub struct Measurements {
    pub kernel_measurement: [u8; 32],
    pub cmdline_measurement: [u8; 32],
    pub setup_data_measurement: [u8; 32],
    pub ram_disk_measurement: [u8; 32],
    pub memory_map_measurement: [u8; 32],
    pub acpi_measurement: [u8; 32],
}

/// Signer implementation.
impl Stage0Signer {
    fn sign(&self, data: &[u8]) -> Vec<u8> {
        let signed_stage1_ca_verifying_key: Signature = self.signing_key.sign(data);
        Vec::from(signed_stage1_ca_verifying_key.to_bytes().as_slice())
    }
}

fn derive_id(ikm: &[u8], info: Option<&[u8]>) -> [u8; KEY_ID_LENGTH] {
    let hkdf = Hkdf::<Sha256>::new(Some(ID_SALT.as_bytes()), ikm);
    let mut okm: [u8; KEY_ID_LENGTH] = [0u8; KEY_ID_LENGTH];
    hkdf.expand(info.unwrap_or(&[]), &mut okm)
        .expect("invalid length for HKDF output");

    okm
}

fn generate_ecdsa_keys(info: &str) -> (SigningKey, [u8; KEY_ID_LENGTH]) {
    let key = SigningKey::random(&mut OsRng);
    let public_key = VerifyingKey::from(&key);
    let key_id = derive_id(
        public_key.to_encoded_point(false).as_bytes(),
        Some(info.as_bytes()),
    );
    (key, key_id)
}
///
/// Generates Stage1 attestation evidence and ECA
fn generate_stage1_certificate(
    stage0_eca_key: SigningKey,
    stage0_cert_issuer: String,
    measurements: &Measurements,
) -> Result<Vec<u8>, CoseError> {
    // Generate Stage 1 keys and Signer.
    let stage1_eca_key = generate_ecdsa_keys(INFO_STR);
    let stage1_eca_verifying_key = VerifyingKey::from(&stage1_eca_key.0);
    let stage0_signer = Stage0Signer {
        signing_key: stage0_eca_key,
    };

    let encoded_point = stage1_eca_verifying_key.to_encoded_point(false);
    let x = encoded_point.x();
    let y = encoded_point.y();

    let stage1_eca_verifying_cose_key = CoseKey {
        kty: KeyType::Assigned(iana::KeyType::EC2),
        key_id: Vec::from(stage1_eca_key.1),
        alg: Some(Algorithm::Assigned(iana::Algorithm::ES384)),
        key_ops: vec![KeyOperation::Assigned(iana::KeyOperation::Verify)]
            .into_iter()
            .collect(),
        params: vec![
            (
                Label::Int(iana::Ec2KeyParameter::Crv as i64),
                Value::from(iana::EllipticCurve::P_384 as u64),
            ),
            (
                Label::Int(iana::Ec2KeyParameter::X as i64),
                Value::Bytes(x.unwrap().to_vec()),
            ),
            (
                Label::Int(iana::Ec2KeyParameter::Y as i64),
                Value::Bytes(y.unwrap().to_vec()),
            ),
        ],
        ..Default::default()
    };

    // Setting bit 5 in little-endian order to 1 for keyCertSign usage. For more details
    // refer: https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.3
    let key_usage: [u8; 2] = [0x20, 0x00];
    // Generate claims and add the Stage1 CA key.
    let claims = cwt::ClaimsSetBuilder::new()
        .issuer(stage0_cert_issuer)
        .subject(hex::encode(stage1_eca_key.1))
        // Add additional private-use claim.
        .private_claim(
            SUBJECT_PUBLIC_KEY_ID,
            Value::Bytes(stage1_eca_verifying_cose_key.to_vec().unwrap()),
        )
        .private_claim(KEY_USAGE_ID, Value::Bytes(Vec::from(key_usage)))
        .private_claim(
            KERNEL_MEASUREMENT_ID,
            Value::Bytes(Vec::from(measurements.kernel_measurement)),
        )
        .private_claim(
            KERNEL_COMMANDLINE_MEASUREMENT_ID,
            Value::Bytes(Vec::from(measurements.cmdline_measurement)),
        )
        .private_claim(
            SETUP_DATA_MEASUREMENT_ID,
            Value::Bytes(Vec::from(measurements.setup_data_measurement)),
        )
        .private_claim(
            INITRD_MEASUREMENT_ID,
            Value::Bytes(Vec::from(measurements.ram_disk_measurement)),
        )
        .private_claim(
            MEMORY_MAP_MEASUREMENT_ID,
            Value::Bytes(Vec::from(measurements.memory_map_measurement)),
        )
        .private_claim(
            ACPI_MEASUREMENT_ID,
            Value::Bytes(Vec::from(measurements.acpi_measurement)),
        )
        .build();

    let aad = b"";

    // Build a `CoseSign1` object.
    let protected = coset::HeaderBuilder::new()
        .algorithm(iana::Algorithm::ES384)
        .build();
    let unprotected = coset::HeaderBuilder::new()
        .key_id((*b"AsymmetricECDSA384").into())
        .build();
    let sign1 = coset::CoseSign1Builder::new()
        .protected(protected)
        .unprotected(unprotected)
        .payload(claims.clone().to_vec()?)
        .create_signature(aad, |data| stage0_signer.sign(data))
        .build();
    sign1.to_vec()
}

/// Generate signed attestation for the 'measurements' of all Stage 1 components.
pub fn generate_stage1_attestation(measurements: &Measurements) {
    // Generate Stage0 keys. This key will be used to sign Stage1
    // measurement+config and the stage1_ca_key.
    let stage0_eca_key = generate_ecdsa_keys(INFO_STR);
    let stage0_eca_verifying_key = VerifyingKey::from(&stage0_eca_key.0);

    // Call generate_attestation_report() to get 'stage0_ca_verifying_key' added to attestation
    // report.
    log::debug!(
        "Stage0 Verification key: {}",
        hex::encode(stage0_eca_verifying_key.to_encoded_point(false).as_bytes())
    );

    // Generate Stage1 CWT.
    let stage1_eca = generate_stage1_certificate(
        stage0_eca_key.0,
        hex::encode(stage0_eca_key.1),
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
