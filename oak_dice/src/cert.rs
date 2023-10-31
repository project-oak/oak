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

//! Constants and helper functions to work with CWT-based DICE certificates.

use alloc::{string::String, vec, vec::Vec};
use coset::{
    cbor::value::Value,
    cwt::{ClaimName, ClaimsSet, ClaimsSetBuilder},
    iana, Algorithm, CborSerializable, CoseError, CoseKey, CoseSign1, KeyOperation, KeyType, Label,
};
use hkdf::Hkdf;
use p256::ecdsa::{signature::Signer, Signature, SigningKey, VerifyingKey};
use rand_core::OsRng;
use sha2::Sha256;

/// Length of the unique ID for ECDSA keys generated.
pub const KEY_ID_LENGTH: usize = 20;
/// ID for the CWT private claim corresponding to the Subject of the CWT.
pub const SUBJECT_PUBLIC_KEY_ID: i64 = -4670552;
/// ID for the bitstring used to describe the intended usage for the key represented by the
/// certificate.
pub const KEY_USAGE_ID: i64 = -4670553;
/// ID for the CWT private claim ID corresponding to the VM kernel measurement.
pub const KERNEL_MEASUREMENT_ID: i64 = -4670555;
/// ID for the CWT private claim ID corresponding to the VM kernel command-line measurement.
pub const KERNEL_COMMANDLINE_MEASUREMENT_ID: i64 = -4670556;
/// ID for the CWT private claim ID corresponding to the VM kernel setup data measurement.
pub const SETUP_DATA_MEASUREMENT_ID: i64 = -4670557;
/// ID for the CWT private claim ID corresponding to the initial RAM disk measurement.
pub const INITRD_MEASUREMENT_ID: i64 = -4670558;
/// ID for the CWT private claim ID corresponding to the physical memory map (e820 table).
pub const MEMORY_MAP_MEASUREMENT_ID: i64 = -4670559;
/// ID for the CWT private claim ID corresponding to the hash of the commands for building the ACPI
/// tables.
pub const ACPI_MEASUREMENT_ID: i64 = -4670560;
/// ID for the CWT private claim label corresponding to the hash of the binary for the layer in the
/// case where a single binary is measured for a layer..
pub const CODE_DIGEST_ID: i64 = -4670545;

/// String to be used as salt for generating Key IDs.
const ID_SALT: &[u8] = b"DICE_ID_SALT";
/// Info string for HKDF generator.
const INFO_STR: &[u8] = b"ID";
/// Empty additional data.
const EMPTY_ADDITIONAL_DATA: &[u8] = b"";

bitflags::bitflags! {
    /// Intended usage of a key.
    ///
    /// See: https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.3 for more details.
    #[derive(Clone, Copy, Debug)]
    pub struct KeyUsage: u16 {
        const DIGITAL_SIGNATURE = 1 << 0;
        const CONTENT_COMMITMENT = 1 << 1;
        const KEY_ENCIPHERMENT = 1 << 2;
        const DATA_ENCIPHERMENT = 1 << 3;
        const KEY_AGREEMENT = 1 << 4;
        const KEY_CERT_SIGN = 1<< 5;
        const CRL_SIGN = 1 << 6;
        const ENCIPHER_ONLY = 1 << 7;
        const DECIPHER_ONLY = 1 << 8;
    }
}

/// Derives an ID from a public key.
pub fn derive_public_key_id(public_key: &VerifyingKey) -> [u8; KEY_ID_LENGTH] {
    let ikm = public_key.to_encoded_point(false);
    let hkdf = Hkdf::<Sha256>::new(Some(ID_SALT), ikm.as_bytes());
    let mut result = [0u8; KEY_ID_LENGTH];
    hkdf.expand(INFO_STR, &mut result)
        .expect("invalid length for HKDF output");
    result
}

/// Generates private/public ECDSA key pair.
pub fn generate_ecdsa_key_pair() -> (SigningKey, VerifyingKey) {
    let private_key = SigningKey::random(&mut OsRng);
    let public_key = VerifyingKey::from(&private_key);
    (private_key, public_key)
}

/// Converts an ECDSA verifying key to a COSE_Key representation.
pub fn public_key_to_cose_key(public_key: &VerifyingKey) -> CoseKey {
    let encoded_point = public_key.to_encoded_point(false);
    CoseKey {
        kty: KeyType::Assigned(iana::KeyType::EC2),
        key_id: Vec::from(derive_public_key_id(public_key)),
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
                Value::Bytes(encoded_point.x().unwrap().to_vec()),
            ),
            (
                Label::Int(iana::Ec2KeyParameter::Y as i64),
                Value::Bytes(encoded_point.y().unwrap().to_vec()),
            ),
        ],
        ..Default::default()
    }
}

/// Generates a CWT certificate representing an embedded certificate authority (ECA) with its
/// private key.
///
///  # Arguments
///
/// * `issuer_eca_key` - The private key that the issuer uses to sign issued certificates.
/// * `issuer_id` - A string identifying the key used by the issuer. This would typically be the hex
///   encoding of the output from calling `derive_public_key_id` using the issuer's public key.
/// * `additional_claims` - Any additional claims that must be included in the certificate. This is
///   typically used to provide measurements of the components in the layer associated with th
///   certificate.
pub fn generate_eca_certificate(
    issuer_eca_key: &SigningKey,
    issuer_id: String,
    additional_claims: Vec<(ClaimName, Value)>,
) -> Result<(CoseSign1, SigningKey), CoseError> {
    let (signing_key, verifying_key) = generate_ecdsa_key_pair();
    let verifying_key_id = hex::encode(derive_public_key_id(&verifying_key));
    let mut claim_builder = ClaimsSetBuilder::new()
        .issuer(issuer_id)
        .subject(verifying_key_id)
        .private_claim(
            SUBJECT_PUBLIC_KEY_ID,
            Value::Bytes(public_key_to_cose_key(&verifying_key).to_vec().unwrap()),
        )
        .private_claim(
            KEY_USAGE_ID,
            Value::Bytes(KeyUsage::KEY_CERT_SIGN.bits().to_le_bytes().into()),
        );

    for (claim_name, value) in additional_claims.into_iter() {
        claim_builder = match claim_name {
            ClaimName::PrivateUse(id) => claim_builder.private_claim(id, value),
            ClaimName::Assigned(assigned_name) => claim_builder.claim(assigned_name, value),
            ClaimName::Text(name) => claim_builder.text_claim(name, value),
        }
    }

    let protected = coset::HeaderBuilder::new()
        .algorithm(iana::Algorithm::ES384)
        .build();
    let unprotected = coset::HeaderBuilder::new()
        .key_id((*b"AsymmetricECDSA384").into())
        .build();
    Ok((
        coset::CoseSign1Builder::new()
            .protected(protected)
            .unprotected(unprotected)
            .payload(claim_builder.build().to_vec()?)
            .create_signature(EMPTY_ADDITIONAL_DATA, |data| {
                let signature: Signature = issuer_eca_key.sign(data);
                signature.to_bytes().as_slice().into()
            })
            .build(),
        signing_key,
    ))
}

/// Parses a bytes slice as a CWT certificate and extracts the payload as a set of claims.
pub fn get_claims_set_from_certifcate_bytes(bytes: &[u8]) -> Result<ClaimsSet, CoseError> {
    let cwt = CoseSign1::from_slice(bytes)?;
    let payload = cwt.payload.unwrap_or_default();
    ClaimsSet::from_slice(&payload)
}
