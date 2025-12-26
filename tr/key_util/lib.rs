//
// Copyright 2025 The Project Oak Authors
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

#![no_std]

extern crate alloc;

use alloc::{string::String, vec::Vec};
use core::{
    cmp::{Ord, Ordering},
    iter::Iterator,
};

use anyhow::Ok;
use ecdsa::signature::Verifier;
use oak_proto_rust::oak::attestation::v1::{KeyType, Signature, VerifyingKeySet};
use p256::pkcs8::{der::Decode, DecodePublicKey};

const PUBLIC_KEY_PEM_LABEL: &str = "PUBLIC KEY";

/// Converts a raw ASN.1 DER public key bytes to PEM with a "PUBLIC KEY" label.
pub fn convert_raw_to_pem(asn1_der_public_key_bytes: &[u8]) -> String {
    let doc = p256::pkcs8::Document::from_der(asn1_der_public_key_bytes)
        .expect("public key bytes are not ASN.1 DER");
    doc.to_pem(PUBLIC_KEY_PEM_LABEL, p256::pkcs8::LineEnding::LF).expect("couldn't create pem")
}

/// Converts a PEM public key to raw ASN.1 DER bytes.
pub fn convert_pem_to_raw(public_key_pem: &str) -> anyhow::Result<Vec<u8>> {
    let (label, key) = p256::pkcs8::Document::from_pem(public_key_pem)
        .map_err(|e| anyhow::anyhow!("Couldn't interpret PEM: {e}"))?;

    anyhow::ensure!(
        label == PUBLIC_KEY_PEM_LABEL,
        "PEM label {label} is not {PUBLIC_KEY_PEM_LABEL}"
    );

    Ok(key.into_vec())
}

/// Converts ASN.1 DER public key bytes to a [`p256::ecdsa::VerifyingKey`].
pub fn convert_raw_to_verifying_key(
    public_key: &[u8],
) -> anyhow::Result<p256::ecdsa::VerifyingKey> {
    let doc = p256::pkcs8::Document::from_der(public_key)
        .map_err(|e| anyhow::anyhow!("Could not interpret bytes as ASN.1 DER: {e}"))?;
    p256::ecdsa::VerifyingKey::from_public_key_der(doc.as_bytes())
        .map_err(|e| anyhow::anyhow!("couldn't convert der to verifying key: {e}"))
}

/// Compares two ECDSA public keys.
///
/// Instead of comparing the bytes, we parse the
/// bytes and compare p256 keys. Keys are considered equal if they are the same
/// on the elliptic curve. This means that the keys could have different bytes,
/// but still be the same key.
pub fn equal_keys(public_key_a: &[u8], public_key_b: &[u8]) -> anyhow::Result<bool> {
    let key_a = convert_raw_to_verifying_key(public_key_a)?;
    let key_b = convert_raw_to_verifying_key(public_key_b)?;
    Ok(key_a.cmp(&key_b) == Ordering::Equal)
}

/// Verifies a signature against a key set, given the signed contents.
pub fn verify_signature(
    signature: &Signature,
    contents: &[u8],
    key_set: &VerifyingKeySet,
) -> anyhow::Result<()> {
    let key = key_set
        .keys
        .iter()
        .find(|k| k.key_id == signature.key_id)
        .ok_or_else(|| anyhow::anyhow!("could not find key id in key set"))?;
    match key.r#type() {
        KeyType::Undefined => anyhow::bail!("Undefined key type"),
        KeyType::EcdsaP256Sha256 => verify_signature_ecdsa(&signature.raw, contents, &key.raw),
    }
}

/// Verifies the signature over the contents using the public key.
pub fn verify_signature_ecdsa(
    signature_der: &[u8],
    contents: &[u8],
    public_key_der: &[u8],
) -> anyhow::Result<()> {
    let sig = ecdsa::Signature::from_der(signature_der)
        .map_err(|error| anyhow::anyhow!("invalid ASN.1 signature: {}", error))?;
    let key = convert_raw_to_verifying_key(public_key_der)
        .map_err(|error| anyhow::anyhow!("couldn't convert public key: {error}"))?;

    key.verify(contents, &sig)
        .map_err(|error| anyhow::anyhow!("couldn't verify signature: {}", error))
}

#[cfg(test)]
mod tests;
