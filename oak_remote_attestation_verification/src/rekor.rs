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

//! This module provides structs for representing a Rekor LogEntry, as well as logic for parsing and
//! verifying signatures in a Rekor LogEntry.

use alloc::{collections::BTreeMap, string::String, vec::Vec};
use anyhow::Context;
use base64::{prelude::BASE64_STANDARD, Engine as _};
use core::{cmp::Ordering, str::FromStr};
use ecdsa::{signature::Verifier, Signature};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Struct representing a Rekor LogEntry.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/log_entry.go#L89.>
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct LogEntry {
    /// We cannot directly use the type `Body` here, since body is Base64-encoded.
    #[serde(rename = "body")]
    pub body: String,

    #[serde(rename = "integratedTime")]
    pub integrated_time: usize,

    /// This is the SHA256 hash of the DER-encoded public key for the log at the time the entry was
    /// included in the log
    /// Pattern: ^[0-9a-fA-F]{64}$
    #[serde(rename = "logID")]
    pub log_id: String,

    /// Minimum: 0
    #[serde(rename = "logIndex")]
    pub log_index: u64,

    /// Includes a signature over the body, integratedTime, logID, and logIndex.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "verification")]
    pub verification: Option<LogEntryVerification>,
}

/// Struct representing the body in a Rekor LogEntry.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Body {
    #[serde(rename = "apiVersion")]
    pub api_version: String,
    pub kind: String,
    pub spec: Spec,
}

/// Struct representing the `spec` in the body of a Rekor LogEntry.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L39.>
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Spec {
    pub data: Data,
    pub signature: GenericSignature,
}

/// Struct representing the hashed data in the body of a Rekor LogEntry.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L179.>
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Data {
    pub hash: Hash,
}

/// Struct representing a hash digest.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L273.>
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Hash {
    pub algorithm: String,
    pub value: String,
}

/// Struct representing a signature in the body of a Rekor LogEntry.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L383>
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct GenericSignature {
    /// Base64 content that is signed.
    pub content: String,
    pub format: String,
    #[serde(rename = "publicKey")]
    pub public_key: PublicKey,
}

/// Struct representing a public key included in the body of a Rekor LogEntry.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L551.>
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct PublicKey {
    /// Base64 content of a public key.
    pub content: String,
}

/// Struct representing a verification object in a Rekor LogEntry. The verification object in Rekor
/// also contains an inclusion proof. Since we currently don't verify the inclusion proof in the
/// client, it is omitted from this struct.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct LogEntryVerification {
    // Base64-encoded signature over the body, integratedTime, logID, and logIndex.
    #[serde(rename = "signedEntryTimestamp")]
    pub signed_entry_timestamp: String,
}

/// Convenient struct for verifying the `signedEntryTimestamp` in a Rekor LogEntry.
///
/// This bundle can be verified using the public key from Rekor. The public key can
/// be obtained from the `/api/v1/log/publicKey` Rest API. For `sigstore.dev`, it is a PEM-encoded
/// x509/PKIX public key. The PEM-encoded content can be parsed into a `p256::ecdsa::VerifyingKey`
/// using `unmarshal_pem_to_p256_public_key`.
pub struct RekorSignatureBundle {
    /// Canonicalized JSON representation, based on RFC 8785 rules, of a subset of a Rekor LogEntry
    /// fields that are signed to generate `signedEntryTimestamp` (also a field in the Rekor
    /// LogEntry). These fields include body, integratedTime, logID and logIndex.
    pub canonicalized: Vec<u8>,

    /// Base64-encoded signature over the canonicalized JSON document.
    pub base64_signature: Vec<u8>,
}

/// Converter for creating a RekorSignatureBundle from a Rekor LogEntry as described in
/// <https://github.com/sigstore/rekor/blob/4fcdcaa58fd5263560a82978d781eb64f5c5f93c/openapi.yaml#L433-L476>.
impl TryFrom<&LogEntry> for RekorSignatureBundle {
    type Error = anyhow::Error;

    fn try_from(log_entry: &LogEntry) -> anyhow::Result<Self> {
        // Create a copy of the LogEntry, but skip the verification.
        let entry_subset = LogEntry {
            body: log_entry.body.clone(),
            integrated_time: log_entry.integrated_time,
            log_id: log_entry.log_id.clone(),
            log_index: log_entry.log_index,
            verification: None,
        };

        // Canonicalized JSON document that is signed. Canonicalization should follow the RFC 8785
        // rules.
        let canonicalized = serde_jcs::to_string(&entry_subset)
            .context("couldn't create canonicalized json string")?;
        let canonicalized = canonicalized.as_bytes().to_vec();

        // Extract the signature from the LogEntry.
        let sig_base64 = log_entry
            .verification
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no verification field in the log entry"))?
            .signed_entry_timestamp
            .clone();
        let base64_signature = sig_base64.as_str().as_bytes().to_vec();

        Ok(Self {
            canonicalized,
            base64_signature,
        })
    }
}

/// Verifies a Rekor LogEntry.
///
/// The verification involves the following:
///
/// 1. verifying the signature in `signedEntryTimestamp`, using Rekor's public key,
/// 1. verifying the signature in `body.RekordObj.signature`, using the endorser's public key,
/// 1. verifying that the content of the body matches the input `endorsement_bytes`.
///
/// Returns `Ok(())` if the verification succeeds, otherwise returns `Err()`.
pub fn verify_rekor_log_entry(
    log_entry_bytes: &[u8],
    pem_encoded_rekor_public_key_bytes: &[u8],
    endorsement_bytes: &[u8],
) -> anyhow::Result<()> {
    verify_rekor_signature(log_entry_bytes, pem_encoded_rekor_public_key_bytes)?;

    let body = get_rekor_log_entry_body(log_entry_bytes)?;

    // Verify the body in the Rekor LogEntry
    verify_rekor_body(&body, endorsement_bytes)?;

    Ok(())
}

/// Parses the given bytes into a Rekor `LogEntry` object, and returns its `body` parsed into an
/// instance of `Body`.
pub fn get_rekor_log_entry_body(log_entry_bytes: &[u8]) -> anyhow::Result<Body> {
    let parsed: BTreeMap<String, LogEntry> = serde_json::from_slice(log_entry_bytes)
        .context("couldn't parse bytes into a LogEntry object")?;
    let entry = parsed.values().next().context("no entry in the map")?;

    // Parse base64-encoded entry.body into an instance of Body.
    let body_bytes: Vec<u8> = BASE64_STANDARD
        .decode(entry.body.clone())
        .context("couldn't decode Base64 signature")?;

    serde_json::from_slice(&body_bytes).context("couldn't parse bytes into a Body object")
}

/// Parses `log_entry_bytes` into a Rekor LogEntry, and verifies the signature in
/// signedEntryTimestamp using the public key in `pem_encoded_public_key_bytes`.
///
/// `log_entry_bytes`: LogEntry downloaded from Rekor as a byte array.
/// `pem_encoded_public_key_bytes`: PEM-encoded public key of Rekor as a byte array.
///
/// Returns `Ok(())` if the verification succeeds, otherwise returns `Err()`.
pub fn verify_rekor_signature(
    log_entry_bytes: &[u8],
    pem_encoded_rekor_public_key_bytes: &[u8],
) -> anyhow::Result<()> {
    let signature_bundle = rekor_signature_bundle(log_entry_bytes)?;

    verify_signature(
        &signature_bundle.base64_signature,
        &signature_bundle.canonicalized,
        pem_encoded_rekor_public_key_bytes,
    )
    .context("couldn't verify signedEntryTimestamp of the Rekor LogEntry")
}

/// Verifies the signature in the `body` over the `contents_bytes`, using the public key in
/// `pem_encoded_public_key_bytes`.
///
/// Returns `Ok(())` if the verification succeeds, otherwise returns `Err()`.
pub fn verify_rekor_body(body: &Body, contents_bytes: &[u8]) -> anyhow::Result<()> {
    if body.spec.signature.format != "x509" {
        anyhow::bail!(
            "unsupported signature format: {}; only x509 is supported",
            body.spec.signature.format
        )
    }

    // For now, we only support `sha256` as the hashing algorithm.
    if body.spec.data.hash.algorithm != "sha256" {
        anyhow::bail!(
            "unsupported hash algorithm: {}; only sha256 is supported",
            body.spec.data.hash.algorithm
        )
    }

    // Check that hash of the endorsement statement matches the hash of the data in the Body.
    let contents_hash = get_sha256(contents_bytes);
    let contents_hash_hex = hex::encode(contents_hash);
    if contents_hash_hex != body.spec.data.hash.value {
        anyhow::bail!(
            "the hash of the endorsement file ({:?}) does not match the hash of the data in the body of the rekor entry ({:?})",
            contents_hash_hex,
            body.spec.data.hash.value
        )
    }

    let public_key_bytes: Vec<u8> = BASE64_STANDARD
        .decode(body.spec.signature.public_key.content.as_bytes())
        .expect("couldn't base64-decode the public key bytes in the Rekor LogEntry body");

    verify_signature(
        body.spec.signature.content.as_str().as_bytes(),
        contents_bytes,
        &public_key_bytes,
    )
    .context("couldn't verify signature over the endorsement file")
}

/// Verifies the given base64-encoded signature over the given data bytes, using the given
/// PEM-encoded public key.
///
/// Returns `Ok(())` if the verification succeeds, otherwise returns `Err()`.
pub fn verify_signature(
    base64_signature_bytes: &[u8],
    content_bytes: &[u8],
    pem_encoded_public_key_bytes: &[u8],
) -> anyhow::Result<()> {
    let sig: Vec<u8> = BASE64_STANDARD
        .decode(base64_signature_bytes)
        .context("couldn't decode Base64 signature")?;
    let signature = Signature::from_der(&sig).context("invalid ASN.1 signature")?;
    let key = unmarshal_pem_to_p256_public_key(pem_encoded_public_key_bytes)?;

    key.verify(content_bytes, &signature)
        .context("couldn't verify signature")
}

/// Parses a PEM-encoded x509/PKIX public key into a `p256::ecdsa::VerifyingKey`.
///
/// `pem_bytes`: A PEM-encoded public key as a byte array.
pub fn unmarshal_pem_to_p256_public_key(
    pem_bytes: &[u8],
) -> anyhow::Result<p256::ecdsa::VerifyingKey> {
    let pem_str = core::str::from_utf8(pem_bytes).context("couldn't convert bytes to string")?;
    p256::ecdsa::VerifyingKey::from_str(pem_str)
        .context("couldn't parse pem as a p256::ecdsa::VerifyingKey")
}

fn rekor_signature_bundle(log_entry_bytes: &[u8]) -> anyhow::Result<RekorSignatureBundle> {
    let parsed: BTreeMap<String, LogEntry> = serde_json::from_slice(log_entry_bytes)
        .context("couldn't parse bytes into a LogEntry object")?;
    let entry = parsed.values().next().context("no entry in the map")?;

    RekorSignatureBundle::try_from(entry)
}

/// Compares two pem-encoded ECDSA public keys. Instead of comparing the bytes, we parse the bytes
/// and compare p256 keys. Keys are considered equal if they are the same on the elliptic curve.
/// This means that the keys could have different bytes, but still be the same key.
pub fn compare_keys(
    public_key_bytes_a: &[u8],
    public_key_bytes_b: &[u8],
) -> anyhow::Result<Ordering> {
    let key_a = unmarshal_pem_to_p256_public_key(public_key_bytes_a)?;
    let key_b = unmarshal_pem_to_p256_public_key(public_key_bytes_b)?;

    Ok(key_a.cmp(&key_b))
}

/// Computes a SHA-256 digest of `input` and returns it in a form of raw bytes.
/// Returns the hash as a 32-bytes array.
pub fn get_sha256(input: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(input);
    hasher.finalize().into()
}
