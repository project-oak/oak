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

//! This module provides structs for representing a Rekor LogEntry, as well as
//! logic for parsing and verifying signatures in a Rekor LogEntry.

extern crate alloc;

use alloc::{collections::BTreeMap, format, string::String, vec::Vec};

use anyhow::Context;
use base64::{prelude::BASE64_STANDARD, Engine as _};
use digest_util::hash_sha2_256;
use key_util::{convert_pem_to_raw, verify_signature_ecdsa};
use oak_proto_rust::oak::attestation::v1::VerifyingKeySet;
use oak_time::Instant;
use serde::{Deserialize, Serialize};

use crate::util::verify_timestamp;

/// Struct representing a Rekor LogEntry. See
/// <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/log_entry.go#L89>
/// <https://github.com/sigstore/rekor/blob/4fcdcaa58fd5263560a82978d781eb64f5c5f93c/openapi.yaml#L433-L476>
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
pub struct LogEntry {
    /// We cannot directly use the type `Body` here, since body is
    /// Base64-encoded.
    #[serde(rename = "body")]
    pub body: String,

    // The timestamp when this entry was added to the log. In seconds since
    // Unix Epoch UTC.
    #[serde(rename = "integratedTime")]
    pub integrated_time: usize,

    /// This is the SHA256 hash of the DER-encoded public key for the log at the
    /// time the entry was included in the log
    /// Pattern: ^[0-9a-fA-F]{64}$
    #[serde(rename = "logID")]
    pub log_id: String,

    /// The serial number in the index; starts counting from zero.
    #[serde(rename = "logIndex")]
    pub log_index: u64,

    /// Includes a signature over the body, integratedTime, logID, and logIndex.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "verification")]
    pub verification: Option<LogEntryVerification>,
}

/// Struct representing the body in a Rekor LogEntry.
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct Body {
    #[serde(rename = "apiVersion")]
    pub api_version: String,
    pub kind: String,
    pub spec: Spec,
}

/// Struct representing the `spec` in the body of a Rekor LogEntry.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L39.>
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct Spec {
    pub data: Data,
    pub signature: GenericSignature,
}

/// Struct representing the hashed data in the body of a Rekor LogEntry.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L179.>
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct Data {
    pub hash: Hash,
}

/// Struct representing a hash digest.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L273.>
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct Hash {
    /// The algorithm used for this hash. Example: `sha256`.
    pub algorithm: String,

    /// The hex-encoded value of the hash specified via the `algorithm` field.
    pub value: String,
}

/// Struct representing a signature in the body of a Rekor LogEntry.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L383>
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct GenericSignature {
    /// Base64-encoded content that is signed.
    pub content: String,

    /// The format of the signature. Example: `x509`.
    pub format: String,

    /// The public key to verify the signature.
    #[serde(rename = "publicKey")]
    pub public_key: PublicKey,
}

/// Struct representing a public key included in the body of a Rekor LogEntry.
/// Based on <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L551.>
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct PublicKey {
    /// Base64-encoded public key.
    pub content: String,
}

/// Struct representing a verification object in a Rekor LogEntry. The
/// verification object in Rekor also contains an inclusion proof. Since we
/// currently don't verify the inclusion proof in the client, it is omitted from
/// this struct.
#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub struct LogEntryVerification {
    // Base64-encoded signature over the body, integratedTime, logID, and logIndex.
    #[serde(rename = "signedEntryTimestamp")]
    pub signed_entry_timestamp: String,
}

/// Verifies a Rekor log entry by key set.
pub fn verify_rekor_log_entry(
    serialized_log_entry: &[u8],
    rekor_key_set: &VerifyingKeySet,
    serialized_endorsement: &[u8],
    now_utc_millis: i64,
) -> anyhow::Result<()> {
    let log_entry = parse_rekor_log_entry(serialized_log_entry)?;

    if !rekor_key_set.keys.iter().any(|k| verify_rekor_signature(&log_entry, &k.raw).is_ok()) {
        anyhow::bail!("could not verify rekor signature");
    }

    // If the TimestampReferenceValues field is set, we need to validate the time
    // the Rekor log was integrated.
    if let Some(signed_timestamp) = &rekor_key_set.signed_timestamp {
        let current_time = Instant::from_unix_millis(now_utc_millis);
        let timestamp = Instant::from_unix_seconds(log_entry.integrated_time.try_into()?);
        verify_timestamp(current_time, timestamp, signed_timestamp)
            .context("verifying rekor integrate timestamp")?;
    }

    let body = parse_rekor_log_entry_body(&log_entry)?;
    verify_rekor_body(&body, serialized_endorsement)
}

/// Verifies a Rekor LogEntry. This includes verifying:
///
/// 1. the signature in `signedEntryTimestamp` using Rekor's public key,
/// 2. the signature in `body.RekordObj.signature` using the endorser's public
///    key,
/// 3. that the content of the body equals `endorsement`.
pub fn verify_rekor_log_entry_ecdsa(
    serialized_log_entry: &[u8],
    rekor_public_key: &[u8],
    serialized_endorsement: &[u8],
) -> anyhow::Result<()> {
    let log_entry = parse_rekor_log_entry(serialized_log_entry)?;

    verify_rekor_signature(&log_entry, rekor_public_key)?;

    let body = parse_rekor_log_entry_body(&log_entry)?;
    verify_rekor_body(&body, serialized_endorsement)
}

/// Verifies the signature in the body over the contents.
fn verify_rekor_body(body: &Body, contents_bytes: &[u8]) -> anyhow::Result<()> {
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

    // Check that hash of the endorsement statement matches the hash of the data in
    // the Body.
    let contents_hash = hash_sha2_256(contents_bytes);
    let contents_hash_hex = hex::encode(contents_hash);
    if contents_hash_hex != body.spec.data.hash.value {
        anyhow::bail!(
            "the hash of the endorsement file ({:?}) does not match the hash of the data in the body of the rekor entry ({:?})",
            contents_hash_hex,
            body.spec.data.hash.value
        )
    }

    let signature: Vec<u8> = BASE64_STANDARD
        .decode(body.spec.signature.content.as_bytes())
        .expect("couldn't decode the signature in the log entry body");

    let public_key_pem_vec: Vec<u8> = BASE64_STANDARD
        .decode(body.spec.signature.public_key.content.as_bytes())
        .expect("couldn't decode the public key in the Rekor LogEntry body");
    let public_key_pem =
        core::str::from_utf8(&public_key_pem_vec).map_err(|error| anyhow::anyhow!(error))?;
    let public_key = convert_pem_to_raw(public_key_pem)?;

    verify_signature_ecdsa(&signature, contents_bytes, &public_key)
        .context("verifying endorsement signature")
}

fn verify_rekor_signature(log_entry: &LogEntry, rekor_public_key: &[u8]) -> anyhow::Result<()> {
    let json = parse_json(log_entry)?;
    let signature = parse_signature(log_entry)?;
    verify_signature_ecdsa(&signature, &json, rekor_public_key).context("verifying rekor signature")
}

pub fn parse_rekor_log_entry(log_entry: &[u8]) -> anyhow::Result<LogEntry> {
    let parsed: BTreeMap<String, LogEntry> = serde_json::from_slice(log_entry)
        .map_err(|error| anyhow::anyhow!("couldn't parse log entry bytes: {error}"))?;
    let log_entry = parsed.values().next().context("unexpected empty map")?;
    Ok((*log_entry).clone())
}

// Parse base64-encoded entry body into structs.
pub fn parse_rekor_log_entry_body(log_entry: &LogEntry) -> anyhow::Result<Body> {
    let body_bytes: Vec<u8> = BASE64_STANDARD
        .decode(log_entry.body.clone())
        .map_err(|error| anyhow::anyhow!("couldn't decode base64 signature: {error}"))?;

    serde_json::from_slice(&body_bytes)
        .map_err(|error| anyhow::anyhow!("couldn't parse log entry body: {error}"))
}

/// JSON representation, canonicalized based on RFC 8785, of the subset of
/// log entry fields that are signed to generate `signedEntryTimestamp`.
fn parse_json(log_entry: &LogEntry) -> anyhow::Result<Vec<u8>> {
    // We hardcode the canonical serialization because serialization with
    // serde_json requires std; if we get the serialization wrong (e.g.,
    // because a string contain characters requiring special escaping), the
    // signature will fail to match. Thus, this should result in incorrectly
    // rejecting some valid signature bundles, not incorrectly accepting valid ones.
    anyhow::ensure!(!log_entry.body.contains('"'), "unexpected quotes in log entry body");
    anyhow::ensure!(!log_entry.log_id.contains('"'), "unexpected quotes in log entry ID");
    let json = format!(
        r#"{{"body":"{body}","integratedTime":{time},"logID":"{id}","logIndex":{index}}}"#,
        body = &log_entry.body,
        time = log_entry.integrated_time,
        id = &log_entry.log_id,
        index = log_entry.log_index
    );
    Ok(json.as_bytes().to_vec())
}

/// Returns the signature over the JSON obtained by `parse_json()`.
fn parse_signature(log_entry: &LogEntry) -> anyhow::Result<Vec<u8>> {
    let sig_base64 = log_entry
        .verification
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no verification field in the log entry"))?
        .signed_entry_timestamp
        .clone();
    let signature = BASE64_STANDARD
        .decode(sig_base64)
        .map_err(|error| anyhow::anyhow!("couldn't decode Base64 signature: {error}"))?;
    Ok(signature)
}

#[cfg(test)]
mod tests;
