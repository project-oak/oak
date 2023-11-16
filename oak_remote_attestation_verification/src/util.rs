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

use alloc::{string::String, vec::Vec};
use anyhow::Context;
use base64::{prelude::BASE64_STANDARD, Engine as _};
use core::{cmp::Ordering, str::FromStr};
use ecdsa::{signature::Verifier, Signature};
use sha2::{Digest, Sha256};

const PEM_HEADER: &str = "-----BEGIN PUBLIC KEY-----";
const PEM_FOOTER: &str = "-----END PUBLIC KEY-----";

/// Makes a plausible guess whether the public key is in PEM format.
pub fn looks_like_pem(maybe_pem: &str) -> bool {
    let p = maybe_pem.trim();
    p.starts_with(PEM_HEADER) && p.ends_with(PEM_FOOTER)
}

/// Converts a pem key to raw. Will panic if it does not like like pem.
pub fn convert_pem_to_raw(public_key_pem: &str) -> anyhow::Result<Vec<u8>> {
    let stripped = public_key_pem
        .trim()
        .strip_prefix(PEM_HEADER)
        .expect("could not find expected header")
        .strip_suffix(PEM_FOOTER)
        .expect("could not find expected footer");
    let remove_newlines = stripped.replace('\n', "");

    Ok(BASE64_STANDARD.decode(remove_newlines)?)
}

pub fn convert_raw_to_pem(public_key: &[u8]) -> String {
    let mut pem = String::from(PEM_HEADER);
    for (i, c) in BASE64_STANDARD.encode(public_key).chars().enumerate() {
        if i % 64 == 0 {
            pem.push('\n');
        }
        pem.push(c);
    }
    pem.push('\n');
    pem.push_str(PEM_FOOTER);
    pem.push('\n');
    pem
}

/// Converts a PEM-encoded x509/PKIX public key to a verifying key.
pub fn convert_pem_to_verifying_key(
    public_key_pem: &str,
) -> anyhow::Result<p256::ecdsa::VerifyingKey> {
    p256::ecdsa::VerifyingKey::from_str(public_key_pem)
        .context("couldn't parse pem as a p256::ecdsa::VerifyingKey")
}

/// Converts a raw public key to a verifying key.
pub fn convert_raw_to_verifying_key(
    public_key: &[u8],
) -> anyhow::Result<p256::ecdsa::VerifyingKey> {
    // Need to figure out how to create a VerifyingKey without the PEM detour.
    let public_key_pem = convert_raw_to_pem(public_key);
    convert_pem_to_verifying_key(&public_key_pem)
}

/// Compares two ECDSA public keys. Instead of comparing the bytes, we parse the bytes
/// and compare p256 keys. Keys are considered equal if they are the same on the elliptic curve.
/// This means that the keys could have different bytes, but still be the same key.
pub fn equal_keys(public_key_a: &[u8], public_key_b: &[u8]) -> anyhow::Result<bool> {
    let key_a = convert_raw_to_verifying_key(public_key_a)?;
    let key_b = convert_raw_to_verifying_key(public_key_b)?;
    Ok(key_a.cmp(&key_b) == Ordering::Equal)
}

/// Verifies the signature over the contents using the public key.
pub fn verify_signature(
    signature: &[u8],
    contents: &[u8],
    public_key: &[u8],
) -> anyhow::Result<()> {
    let signature = Signature::from_der(signature).context("invalid ASN.1 signature")?;
    let key = convert_raw_to_verifying_key(public_key)?;

    key.verify(contents, &signature)
        .context("couldn't verify signature")
}

/// Computes a SHA2-256 digest of `input` and returns it as raw bytes.
pub fn hash_sha2_256(input: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(input);
    hasher.finalize().into()
}
