//
// Copyright 2022 The Project Oak Authors
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

use alloc::{string::String, vec::Vec};
use coset::{cbor::value::Value, cwt, iana, CborSerializable, CoseError};
use hkdf::Hkdf;
use p384::ecdsa::{signature::Signer, Signature, SigningKey, VerifyingKey};
use rand_core::OsRng;
use sha2::Sha256;

pub const ID_SALT: &str = "DICE_ID_SALT";
pub const SIGNATURE_LENGTH: usize = 20;

/// Attestation related functions
///
/// Returns Signed Stage1 key and measurments
struct Stage0Signer {
    signing_key: SigningKey,
}
// Measurements of various components in Stage1 
pub struct Measurements {
    pub kernel_measurement: [u8; 32],
    pub cmdline_measurement: [u8; 32],
    pub setup_data_measurement: [u8; 32],
    pub ram_disk_measurement: [u8; 32],
    pub memory_map_measurement: [u8; 32],
    pub acpi_measurement: [u8; 32],
}

// Signer implementation.
impl Stage0Signer {
    fn sign(&self, data: &[u8]) -> Vec<u8> {
        let signed_stage1_ca_verifying_key: Signature = self.signing_key.sign(data);
        Vec::from(signed_stage1_ca_verifying_key.to_bytes().as_slice())
    }
}

fn derive_id(ikm: &[u8], info: Option<&[u8]>) -> [u8; SIGNATURE_LENGTH] {
    let hkdf = Hkdf::<Sha256>::new(Some(ID_SALT.as_bytes()), ikm);
    let mut okm: [u8; SIGNATURE_LENGTH] = [0u8; SIGNATURE_LENGTH];
    hkdf.expand(info.unwrap_or(&[]), &mut okm)
        .expect("20 is a valid length for Sha256 to output");

    okm
}

fn generate_ecdsa_keys(info: &str) -> (SigningKey, [u8; SIGNATURE_LENGTH]) {
    let key = SigningKey::random(&mut OsRng);
    let public_key = VerifyingKey::from(&key);
    let key_id = derive_id(
        public_key.to_encoded_point(false).as_bytes(),
        Some(info.as_bytes()),
    );
    (key, key_id)
}

fn generate_stage1_ca_cwt(
    stage0_eca_key: SigningKey,
    stage0_cert_id_hex: String,
    measurements: &Measurements,
) -> Result<Vec<u8>, CoseError> {
    // Generate Stage 1 keys and Signer.
    let info_str = "ID";
    let stage1_ca_key = generate_ecdsa_keys(info_str);
    let stage1_ca_verifying_key = VerifyingKey::from(&stage1_ca_key.0);
    let stage0_signer = Stage0Signer {
        signing_key: stage0_eca_key,
    };

    // Generate claims and add the Stage1 CA key.
    let claims = cwt::ClaimsSetBuilder::new()
        .issuer(stage0_cert_id_hex)
        .subject(hex::encode(stage1_ca_key.1))
        .cwt_id(Vec::from(stage1_ca_key.1))
        // Add additional private-use claim.
        .private_claim(
            -4670552,
            Value::Bytes(Vec::from(
                stage1_ca_verifying_key.to_encoded_point(false).as_bytes(),
            )),
        )
        .private_claim(
            -4670555,
            Value::Bytes(Vec::from(measurements.kernel_measurement)),
        )
        .private_claim(
            -4670556,
            Value::Bytes(Vec::from(measurements.kernel_measurement)),
        )
        .private_claim(
            -4670557,
            Value::Bytes(Vec::from(measurements.setup_data_measurement)),
        )
        .private_claim(
            -4670558,
            Value::Bytes(Vec::from(measurements.ram_disk_measurement)),
        )
        .private_claim(
            -4670559,
            Value::Bytes(Vec::from(measurements.memory_map_measurement)),
        )
        .private_claim(
            -4670560,
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

pub fn generate_stage1_attestation(measurements: &Measurements) {
    // Generate Stage0 keys. This key will be used to sign Stage1
    // measurement+config and the stage1_ca_key
    let info_str = "ID";
    let stage0_ca_key = generate_ecdsa_keys(info_str);
    let stage0_ca_verifying_key = VerifyingKey::from(&stage0_ca_key.0);

    // Call generate_attestation_report() to get 'stage0_ca_verifying_key' added to attestation report.
    log::debug!(
        "Stage0 Verification key: {}",
        hex::encode(stage0_ca_verifying_key.to_encoded_point(false).as_bytes())
    );

    // Generate Stage1 CWT
    let stage1_cwt =
        generate_stage1_ca_cwt(stage0_ca_key.0, hex::encode(stage0_ca_key.1), measurements);
    if stage1_cwt.is_ok() {
        // Call code that transmits the serialized cwt to Stage1
        log::debug!("Signing was successful..");
        return;
    }
    log::debug!("Error in signing: {}", stage1_cwt.unwrap_err())
}
