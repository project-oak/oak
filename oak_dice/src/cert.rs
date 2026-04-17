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
    Algorithm, CborOrdering, CborSerializable, CoseError, CoseKey, CoseSign1, KeyOperation,
    KeyType, Label, RegisteredLabelWithPrivate,
    cbor::value::Value,
    cwt::{ClaimName, ClaimsSet, ClaimsSetBuilder},
    iana,
};
use hkdf::Hkdf;
use p256::{
    EncodedPoint, FieldBytes, U256,
    ecdsa::{Signature, SigningKey, VerifyingKey, signature::Signer},
};
use rand_core::OsRng;
use sha2::Sha256;

/// Length of the unique ID for ECDSA keys generated.
pub const KEY_ID_LENGTH: usize = 20;
/// ID for the CWT private claim corresponding to the Subject of the CWT.
pub const SUBJECT_PUBLIC_KEY_ID: i64 = -4670552;
/// ID for the bitstring used to describe the intended usage for the key
/// represented by the certificate.
pub const KEY_USAGE_ID: i64 = -4670553;
/// The CWT private claim ID for the Kernel layer.
pub const KERNEL_LAYER_ID: i64 = -4670555;
/// The CWT private claim ID for an enclave application layer.
pub const ENCLAVE_APPLICATION_LAYER_ID: i64 = -4670556;
/// The CWT private claim ID for the Oak Containers system image.
pub const SYSTEM_IMAGE_LAYER_ID: i64 = -4670557;
/// The CWT private claim ID for the container image.
pub const CONTAINER_IMAGE_LAYER_ID: i64 = -4670559;
/// The CWT private claim ID for the kernel measurement.
pub const KERNEL_MEASUREMENT_ID: i64 = -4670561;
/// The CWT private claim ID for the kernel command-line measurement.
pub const KERNEL_COMMANDLINE_MEASUREMENT_ID: i64 = -4670562;
/// The CWT private claim ID for the raw kernel command-line.
pub const KERNEL_COMMANDLINE_ID: i64 = -4670573;
/// The CWT private claim ID for the kernel setup data measurement.
pub const SETUP_DATA_MEASUREMENT_ID: i64 = -4670563;
/// The CWT private claim ID for the initial RAM file system measurement.
pub const INITRD_MEASUREMENT_ID: i64 = -4670564;
/// The CWT private claim ID for the physical memory map (e820 table).
pub const MEMORY_MAP_MEASUREMENT_ID: i64 = -4670565;
/// The CWT private claim ID for the concatenated hash of the commands for
/// building the ACPI tables.
pub const ACPI_MEASUREMENT_ID: i64 = -4670566;
/// The CWT private claim ID for the measurement of the layer 2 binary.
pub const LAYER_2_CODE_MEASUREMENT_ID: i64 = -4670567;
/// The CWT private claim ID for the measurement of the layer 3 binary.
pub const LAYER_3_CODE_MEASUREMENT_ID: i64 = -4670569;
/// The CWT private claim ID for the measurement of the application or container
/// config.
pub const FINAL_LAYER_CONFIG_MEASUREMENT_ID: i64 = -4670570;
/// The CWT private claim ID for SHA2_256 digests.
pub const SHA2_256_ID: i64 = -4670572;
/// The CWT private claim ID of the Event digest.
pub const EVENT_ID: i64 = -4670573;
/// The CWT private claim ID of the application keys.
pub const APPLICATION_KEY_ID: i64 = -4670574;
/// The CWT private claim ID of the transparent Event digest.
pub const TRANSPARENT_EVENT_ID: i64 = -4670575;

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

/// Derives an ID from a verifying key.
pub fn derive_verifying_key_id(public_key: &VerifyingKey) -> [u8; KEY_ID_LENGTH] {
    let ikm = public_key.to_encoded_point(false);
    let hkdf = Hkdf::<Sha256>::new(Some(ID_SALT), ikm.as_bytes());
    let mut result = [0u8; KEY_ID_LENGTH];
    hkdf.expand(INFO_STR, &mut result).expect("invalid length for HKDF output");
    result
}

/// Derives an ID from an HPKE KEM public key.
pub fn derive_kem_public_key_id(public_key_bytes: &[u8]) -> [u8; KEY_ID_LENGTH] {
    let hkdf = Hkdf::<Sha256>::new(Some(ID_SALT), public_key_bytes);
    let mut result = [0u8; KEY_ID_LENGTH];
    hkdf.expand(INFO_STR, &mut result).expect("invalid length for HKDF output");
    result
}

/// Generates private/public ECDSA key pair.
pub fn generate_ecdsa_key_pair() -> (SigningKey, VerifyingKey) {
    let private_key = SigningKey::random(&mut OsRng);
    let public_key = VerifyingKey::from(&private_key);
    (private_key, public_key)
}

/// Converts a COSE_Key to a serialized HPKE KEM public key.
pub fn cose_key_to_hpke_public_key(cose_key: &CoseKey) -> Result<Vec<u8>, &'static str> {
    if cose_key.kty != KeyType::Assigned(iana::KeyType::OKP) {
        return Err("invalid key type");
    }
    if cose_key.alg != Some(Algorithm::Assigned(iana::Algorithm::ECDH_ES_A256KW)) {
        return Err("invalid algorithm");
    }
    if !cose_key.key_ops.contains(&KeyOperation::Assigned(iana::KeyOperation::WrapKey)) {
        return Err("invalid key operations");
    }
    if !cose_key.params.iter().any(|(label, value)| {
        label == &Label::Int(iana::OkpKeyParameter::Crv as i64)
            && value == &Value::from(iana::EllipticCurve::X25519 as u64)
    }) {
        return Err("invalid elliptic curve");
    }
    cose_key
        .params
        .iter()
        .find_map(|(label, value)| match value {
            Value::Bytes(bytes) if label == &Label::Int(iana::OkpKeyParameter::X as i64) => {
                Some(bytes.to_vec())
            }
            _ => None,
        })
        .ok_or("public key not found")
}

/// Converts a serialized HPKE KEM public key to a COSE_Key representation
pub fn hpke_public_key_to_cose_key(public_key: &[u8]) -> CoseKey {
    CoseKey {
        kty: KeyType::Assigned(iana::KeyType::OKP),
        key_id: Vec::from(derive_kem_public_key_id(public_key)),
        alg: Some(Algorithm::Assigned(iana::Algorithm::ECDH_ES_A256KW)),
        key_ops: vec![KeyOperation::Assigned(iana::KeyOperation::WrapKey)].into_iter().collect(),
        params: vec![
            (
                Label::Int(iana::OkpKeyParameter::Crv as i64),
                Value::from(iana::EllipticCurve::X25519 as u64),
            ),
            (Label::Int(iana::OkpKeyParameter::X as i64), Value::Bytes(public_key.to_vec())),
        ],
        ..Default::default()
    }
}

/// Converts a COSE_Key to a ECDSA verifying key.
pub fn cose_key_to_verifying_key(cose_key: &CoseKey) -> Result<VerifyingKey, &'static str> {
    if cose_key.kty != KeyType::Assigned(iana::KeyType::EC2) {
        return Err("invalid key type");
    }
    if cose_key.alg != Some(Algorithm::Assigned(iana::Algorithm::ES256)) {
        return Err("invalid algorithm");
    }
    if !cose_key.key_ops.contains(&KeyOperation::Assigned(iana::KeyOperation::Verify)) {
        return Err("invalid key operations");
    }
    if !cose_key.params.iter().any(|(label, value)| {
        label == &Label::Int(iana::Ec2KeyParameter::Crv as i64)
            && value == &Value::from(iana::EllipticCurve::P_256 as u64)
    }) {
        return Err("invalid elliptic curve");
    }
    let x = cose_key
        .params
        .iter()
        .find_map(|(label, value)| match value {
            Value::Bytes(bytes) if label == &Label::Int(iana::Ec2KeyParameter::X as i64) => {
                Some(bytes.clone())
            }
            _ => None,
        })
        .ok_or("x component of public key not found")?;
    if x.len() != U256::BYTES {
        return Err("x component of public key has an invalid length");
    }
    let y = cose_key
        .params
        .iter()
        .find_map(|(label, value)| match value {
            Value::Bytes(bytes) if label == &Label::Int(iana::Ec2KeyParameter::Y as i64) => {
                Some(bytes.clone())
            }
            _ => None,
        })
        .ok_or("y component of public key not found")?;
    if y.len() != U256::BYTES {
        return Err("y component of public key has an invalid length");
    }
    let encoded_point = EncodedPoint::from_affine_coordinates(
        FieldBytes::from_slice(&x),
        FieldBytes::from_slice(&y),
        false,
    );
    VerifyingKey::from_encoded_point(&encoded_point)
        .map_err(|_err| "invalid public key coordinates")
}

/// Converts an ECDSA verifying key to a COSE_Key representation.
pub fn verifying_key_to_cose_key(public_key: &VerifyingKey) -> CoseKey {
    let encoded_point = public_key.to_encoded_point(false);
    let mut ck = CoseKey {
        kty: KeyType::Assigned(iana::KeyType::EC2),
        key_id: Vec::from(derive_verifying_key_id(public_key)),
        alg: Some(Algorithm::Assigned(iana::Algorithm::ES256)),
        key_ops: vec![KeyOperation::Assigned(iana::KeyOperation::Verify)].into_iter().collect(),
        params: vec![
            (
                Label::Int(iana::Ec2KeyParameter::Crv as i64),
                Value::from(iana::EllipticCurve::P_256 as u64),
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
    };
    ck.canonicalize(CborOrdering::LengthFirstLexicographic);
    ck
}

/// Generates a CWT certificate representing an ECDSA signing key, such as an
/// embedded certificate authority (ECA), and returns the certificate and its
/// associated private key.
///
/// # Arguments
///
/// * `issuer_eca_key` - The private key that the issuer uses to sign issued
///   certificates.
/// * `issuer_id` - A string identifying the key used by the issuer. This would
///   typically be the hex encoding of the output from calling
///   `derive_verifying_key_id` using the issuer's public key.
/// * `additional_claims` - Any additional claims that must be included in the
///   certificate. This is typically used to provide measurements of the
///   components in the layer associated with th certificate.
pub fn generate_signing_certificate(
    issuer_eca_key: &SigningKey,
    issuer_id: String,
    verifying_key: &VerifyingKey,
    additional_claims: Vec<(ClaimName, Value)>,
) -> Result<CoseSign1, CoseError> {
    generate_certificate(
        issuer_eca_key,
        issuer_id,
        verifying_key_to_cose_key(verifying_key),
        hex::encode(derive_verifying_key_id(verifying_key)),
        additional_claims,
    )
}

/// Generates a CWT certificate representing a Key Encapsulation Mechanism (KEM)
/// for Hybrid Public-Key Encryption (HPKE) from a serialized public key.
///
/// # Arguments
///
/// * `issuer_eca_key` - The private key that the issuer uses to sign issued
///   certificates.
/// * `issuer_id` - A string identifying the key used by the issuer. This would
///   typically be the hex encoding of the output from calling
///   `derive_kem_public_key_id` using the issuer's public key.
/// * `kem_public_key` - The serialized HPKE KEM public key.
/// * `additional_claims` - Any additional claims that must be included in the
///   certificate. This is typically used to provide measurements of the
///   components in the layer associated with th certificate.
pub fn generate_kem_certificate(
    issuer_eca_key: &SigningKey,
    issuer_id: String,
    kem_public_key: &[u8],
    additional_claims: Vec<(ClaimName, Value)>,
) -> Result<CoseSign1, CoseError> {
    generate_certificate(
        issuer_eca_key,
        issuer_id,
        hpke_public_key_to_cose_key(kem_public_key),
        hex::encode(derive_kem_public_key_id(kem_public_key)),
        additional_claims,
    )
}

fn generate_certificate(
    issuer_eca_key: &SigningKey,
    issuer_id: String,
    public_key: CoseKey,
    public_key_id: String,
    additional_claims: Vec<(ClaimName, Value)>,
) -> Result<CoseSign1, CoseError> {
    let mut claim_builder = ClaimsSetBuilder::new()
        .issuer(issuer_id)
        .subject(public_key_id)
        .private_claim(SUBJECT_PUBLIC_KEY_ID, Value::Bytes(public_key.to_vec()?))
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

    let protected = coset::HeaderBuilder::new().algorithm(iana::Algorithm::ES256).build();
    let unprotected = coset::HeaderBuilder::new().key_id((*b"AsymmetricECDSA256").into()).build();
    Ok(coset::CoseSign1Builder::new()
        .protected(protected)
        .unprotected(unprotected)
        .payload(claim_builder.build().to_vec()?)
        .create_signature(EMPTY_ADDITIONAL_DATA, |data| {
            let signature: Signature = issuer_eca_key.sign(data);
            signature.to_bytes().as_slice().into()
        })
        .build())
}

/// Parses a bytes slice as a CWT certificate and extracts the payload as a set
/// of claims.
pub fn get_claims_set_from_certificate_bytes(bytes: &[u8]) -> Result<ClaimsSet, CoseError> {
    let cwt = CoseSign1::from_slice(bytes)?;
    let payload = cwt.payload.unwrap_or_default();
    ClaimsSet::from_slice(&payload)
}

/// Extracts the certified public key from the claims set of a certificate.
pub fn get_public_key_from_claims_set(claims: &ClaimsSet) -> Result<CoseKey, &'static str> {
    let public_key_bytes = claims
        .rest
        .iter()
        .find_map(|(label, value)| match value {
            Value::Bytes(bytes)
                if label == &RegisteredLabelWithPrivate::PrivateUse(SUBJECT_PUBLIC_KEY_ID) =>
            {
                Some(bytes)
            }
            _ => None,
        })
        .ok_or("public key not found")?;
    CoseKey::from_slice(public_key_bytes).map_err(|_cose_err| "couldn't deserialize public key")
}
