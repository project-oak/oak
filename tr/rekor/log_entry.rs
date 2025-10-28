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

//! Provides structs and functions for parsing and verifying Rekor log entries,
//! supporting the `hashedrekord` type. See
//! <https://docs.rs/sigstore/latest/src/sigstore/rekor/models/hashedrekord.rs.html>

extern crate alloc;

use alloc::borrow::ToOwned;

use anyhow::{ensure, Context};
use base64::{prelude::BASE64_STANDARD, Engine as _};
use digest_util::hash_sha2_256;
use key_util::{convert_pem_to_raw, equal_keys, verify_signature_ecdsa};
use oak_proto_rust::oak::attestation::v1::VerifyingKeySet;
use oak_time::Instant;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{
    alloc::{collections::BTreeMap, format, string::String, vec::Vec},
    util::verify_timestamp,
};

const SIGNED_ENTRY_TIMESTAMP_KEY: &str = "SignedEntryTimestamp";
const LOG_ENTRY_PAYLOAD_KEY: &str = "Payload";

/// Represents the Rekor log entry, or payload. See
/// <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/log_entry.go#L89>
/// <https://github.com/sigstore/rekor/blob/d920fad17c98aff21d98036db6a4820542f7d18d/openapi.yaml#L446-L488>
#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
pub struct LogEntry {
    /// The log entry body is base64-encoded in the actual log entry.
    #[serde(rename = "body")]
    pub body: String,

    /// The timestamp when this entry was added to the log. In seconds since the
    /// Unix Epoch.
    #[serde(rename = "integratedTime")]
    pub integrated_time: usize,

    /// The SHA256 hash of the DER-encoded public key for the log at the time
    /// when the entry was included in the log.
    /// Pattern: ^[0-9a-fA-F]{64}$
    #[serde(rename = "logID")]
    pub log_id: String,

    /// The serial number in the index; starts counting from zero.
    #[serde(rename = "logIndex")]
    pub log_index: u64,

    /// Optional structure for verification.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "verification")]
    pub verification: Option<Verification>,
}

impl LogEntry {
    pub fn from_cosign_bundle<T: AsRef<[u8]>>(bundle: T) -> anyhow::Result<LogEntry> {
        let bundle: Value = serde_json::from_slice(bundle.as_ref())?;
        let payload =
            bundle.get(LOG_ENTRY_PAYLOAD_KEY).ok_or(anyhow::anyhow!("malformed bundle"))?;
        let signed =
            bundle.get(SIGNED_ENTRY_TIMESTAMP_KEY).ok_or(anyhow::anyhow!("malformed bundle"))?;

        let signed: String = String::deserialize(signed)?;
        let verification = Verification { signed_entry_timestamp: signed.to_owned() };

        // As per the spec above, the signature of the payload is done over
        // the canonicalized representation of its fields, which means:
        //  * No whitespace
        //  * JSON keys are sorted lexicographically
        // Because serde_json's Value uses a BTreeMap, the sorting property
        // holds for object values.
        let serialized_log_entry = serde_json::to_string(&payload)?;
        let mut reparsed = parse_single_rekor_log_entry(serialized_log_entry.as_bytes())?;
        reparsed.verification = Some(verification);
        Ok(reparsed)
    }

    /// Parses the base64-encoded log entry body into a struct.
    pub fn body(&self) -> anyhow::Result<Body> {
        let body_bytes: Vec<u8> = BASE64_STANDARD
            .decode(&self.body)
            .map_err(|_| anyhow::anyhow!("failed to decode log entry body"))?;
        serde_json::from_slice(&body_bytes)
            .map_err(|error| anyhow::anyhow!("couldn't parse log entry body: {error}"))
    }

    /// Returns the public key from the log entry.
    pub fn get_public_key(&self) -> anyhow::Result<Vec<u8>> {
        let body = self.body()?;
        let c = body.spec.signature.public_key.content;
        let public_key_pem_vec: Vec<u8> = BASE64_STANDARD
            .decode(c)
            .map_err(|_| anyhow::anyhow!("failed to base64-decode public key"))?;
        let public_key_pem = core::str::from_utf8(&public_key_pem_vec)
            .map_err(|_| anyhow::anyhow!("failed to convert public key to string"))?;
        convert_pem_to_raw(public_key_pem)
    }

    /// Compares the given endorser key with the one in the log entry.
    ///
    /// This check is not performed as part of verify_rekor_log_entry_*; it
    /// needs to be done explicitly.
    pub fn compare_public_key(&self, public_key: &[u8]) -> anyhow::Result<()> {
        let self_public_key = self.get_public_key()?;
        if !equal_keys(&self_public_key, public_key)? {
            anyhow::bail!(
                "endorser public key mismatch: expected {:?} found {:?}",
                public_key,
                &self_public_key,
            )
        }
        Ok(())
    }
}

/// Represents the body of a Rekor log entry.
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct Body {
    /// The version as e.g. "0.0.1".
    #[serde(rename = "apiVersion")]
    pub api_version: String,

    /// The Rekor type. For our purposes this is either "hashedrekord"
    /// (preferred) or "rekord" (deprecated).
    pub kind: String,

    /// Instance of the type following a JSON schema.
    pub spec: Spec,
}

/// Represents the `spec` in the body of a Rekor log entry.
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct Spec {
    pub data: Data,
    pub signature: GenericSignature,
}

/// Represents the hashed data in the body of a Rekor log entry.
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct Data {
    pub hash: Hash,
}

/// Represents a hash obtained via a certain algorithm.
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct Hash {
    /// The algorithm used for this hash. Example: "sha256".
    pub algorithm: String,

    /// The hex-encoded value of the hash specified via the `algorithm` field.
    pub value: String,
}

/// Represents a signature in the body of a Rekor log entry.
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct GenericSignature {
    /// Base64-encoded content that is signed.
    pub content: String,

    /// The public key to verify the signature.
    #[serde(rename = "publicKey")]
    pub public_key: PublicKey,
}

/// Represents a public key in the Rekor log entry body.
#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct PublicKey {
    /// Base64-encoded public key.
    pub content: String,
}

/// Represents a verification object in a Rekor log entry. Since we currently
/// don't verify the inclusion proof, the associated fields are not mentioned
/// or deserialized.
#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub struct Verification {
    // Base64-encoded signature over body, integratedTime, logID, logIndex.
    #[serde(rename = "signedEntryTimestamp")]
    pub signed_entry_timestamp: String,
}

/// Verifies a Rekor log entry by key set and current time.
///
/// # Arguments
///
/// * `serialized_log_entry`: The Rekor log entry that should be verified.
/// * `key_set`: Rekor's verifying key wrapped in a reference value. May also
///   contain reference value for time-based verification.
/// * `artifact_bytes`: The artifact or subject this log entry is about. Likely
///   a serialized endorsement.
/// * `now_utc_millis`: The current time in milliseconds since Unix Epoch, if
///   timestamp verification is requested in the reference value.
///
/// # Returns
///
/// The parsed log entry structure.
pub fn verify_rekor_log_entry(
    serialized_log_entry: &[u8],
    key_set: &VerifyingKeySet,
    artifact_bytes: &[u8],
    now_utc_millis: i64,
) -> anyhow::Result<LogEntry> {
    let log_entry =
        parse_rekor_log_entry(serialized_log_entry).context("parsing Rekor log entry")?;

    if !key_set.keys.iter().any(|k| verify_rekor_signature(&log_entry, &k.raw).is_ok()) {
        anyhow::bail!("could not verify rekor signature");
    }

    // If the TimestampReferenceValues field is set, we need to validate the
    // time the Rekor log was integrated.
    if let Some(signed_timestamp) = &key_set.signed_timestamp {
        let current_time = Instant::from_unix_millis(now_utc_millis);
        let timestamp = Instant::from_unix_seconds(log_entry.integrated_time.try_into()?);
        verify_timestamp(current_time, timestamp, signed_timestamp)
            .context("verifying rekor integrate timestamp")?;
    }

    let body = log_entry.body()?;
    verify_rekor_body(&body, artifact_bytes).context("verifying Rekor body")?;
    Ok(log_entry)
}

/// Verifies a Rekor log entry.
///
/// Contains a subset of the checks `verify_rekor_log_entry`: exactly the
/// time stamp verification is missing. Steps include:
///
/// 1. the signature in `signedEntryTimestamp` using Rekor's public key,
/// 2. the signature in `body.RekordObj.signature` using the endorser's public
///    key,
/// 3. that the content of the body equals `artifact_bytes`.
///
/// # Arguments
///
/// * `serialized_log_entry`: The log entry that should be verified.
/// * `rekor_public_key`: Rekor's verifying key in raw format.
/// * `artifact_bytes`: The artifact or subject this log entry is about. Likely
///   a serialized endorsement.
///
/// # Returns
///
/// The parsed log entry structure.
pub fn verify_rekor_log_entry_ecdsa(
    serialized_log_entry: &[u8],
    rekor_public_key: &[u8],
    artifact_bytes: &[u8],
) -> anyhow::Result<LogEntry> {
    let log_entry =
        parse_rekor_log_entry(serialized_log_entry).context("parsing Rekor log entry")?;
    verify_rekor_signature(&log_entry, rekor_public_key).context("verifying Rekor signature")?;

    let body = log_entry.body()?;
    verify_rekor_body(&body, artifact_bytes).context("verifying Rekor body")?;
    Ok(log_entry)
}

/// Verifies the signature in the log entry body.
///
/// # Arguments
///
/// * `body`: The log entry body.
/// * `artifact_bytes` The underlying artifact or endorsement.
fn verify_rekor_body(body: &Body, artifact_bytes: &[u8]) -> anyhow::Result<()> {
    // TODO: b/445876203 - Reject type "rekord" at some point in the future.
    ensure!(
        body.kind == "rekord" || body.kind == "hashedrekord",
        "unsupported Rekor type: {}",
        body.kind
    );
    ensure!(
        body.spec.data.hash.algorithm == "sha256",
        "unsupported hashing algorithm: {}",
        body.spec.data.hash.algorithm
    );
    let artfifact_hash = hex::encode(hash_sha2_256(artifact_bytes));
    ensure!(
        artfifact_hash == body.spec.data.hash.value,
        "hash of artifact ({:?}) does not match hash in Rekor log entry ({:?})",
        artfifact_hash,
        body.spec.data.hash.value
    );

    let signature: Vec<u8> = BASE64_STANDARD
        .decode(body.spec.signature.content.as_bytes())
        .map_err(|_| anyhow::anyhow!("failed to base64-decode signature"))?;
    let public_key_pem_vec: Vec<u8> = BASE64_STANDARD
        .decode(body.spec.signature.public_key.content.as_bytes())
        .map_err(|_| anyhow::anyhow!("failed to base64-decode public key"))?;
    let public_key_pem = core::str::from_utf8(&public_key_pem_vec)
        .map_err(|_| anyhow::anyhow!("failed to convert public key to string"))?;
    let public_key = convert_pem_to_raw(public_key_pem)?;

    verify_signature_ecdsa(&signature, artifact_bytes, &public_key)
        .context("verifying endorsement signature")
}

/// Verifies Rekor's signature over the log entry.
fn verify_rekor_signature(log_entry: &LogEntry, rekor_public_key: &[u8]) -> anyhow::Result<()> {
    let json = create_canonical_json(log_entry)?;
    let signature = parse_rekor_signature(log_entry)?;
    verify_signature_ecdsa(&signature, &json, rekor_public_key).context("verifying rekor signature")
}

/// Parses a map of ID to serialized Rekor log entries and returns the
/// first value (which is expected to be the only one). The entry UUIDs
/// appearing as map keys are dropped.
pub fn parse_rekor_log_entry(serialized_log_entry: &[u8]) -> anyhow::Result<LogEntry> {
    let parsed: BTreeMap<String, LogEntry> = serde_json::from_slice(serialized_log_entry)
        .map_err(|error| anyhow::anyhow!("couldn't parse log entry map: {error}"))?;
    let log_entry = parsed.values().next().context("unexpected empty map")?;
    Ok((*log_entry).clone())
}

/// Parses a single serialized Rekor log entry into a struct.
fn parse_single_rekor_log_entry(serialized_log_entry: &[u8]) -> anyhow::Result<LogEntry> {
    let parsed: LogEntry = serde_json::from_slice(serialized_log_entry)
        .map_err(|error| anyhow::anyhow!("couldn't parse log entry bytes: {error}"))?;
    Ok(parsed)
}

/// Serializes the log entry into bytes which can be parsed again.
/// Note that the UUID is lost on first parsing.
pub fn serialize_rekor_log_entry(log_entry: &LogEntry) -> anyhow::Result<Vec<u8>> {
    let map: BTreeMap<String, LogEntry> =
        BTreeMap::from([("unknown_uuid".to_owned(), log_entry.clone())]);
    Ok(serde_json::to_vec(&map)?)
}

/// Creates a JSON representation, canonicalized based on RFC 8785, of a
/// subset of log entry fields. Rekor signs the result which then makes up
/// the `signedEntryTimestamp`.
fn create_canonical_json(log_entry: &LogEntry) -> anyhow::Result<Vec<u8>> {
    // We hardcode the canonical serialization because serialization with
    // serde_json requires std; if we get the serialization wrong (e.g.,
    // because a string contain characters requiring special escaping), the
    // signature will fail to match. Thus, this should result in incorrectly
    // rejecting some valid signature bundles, not incorrectly accepting
    // valid ones.
    ensure!(!log_entry.body.contains('"'), "unexpected quotes in log entry body");
    ensure!(!log_entry.log_id.contains('"'), "unexpected quotes in log entry ID");
    let json = format!(
        r#"{{"body":"{body}","integratedTime":{time},"logID":"{id}","logIndex":{index}}}"#,
        body = &log_entry.body,
        time = log_entry.integrated_time,
        id = &log_entry.log_id,
        index = log_entry.log_index
    );
    Ok(json.as_bytes().to_vec())
}

/// Returns Rekor's signature over the canonicalized JSON.
fn parse_rekor_signature(log_entry: &LogEntry) -> anyhow::Result<Vec<u8>> {
    let sig_base64 = &log_entry
        .verification
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no verification field in the log entry"))?
        .signed_entry_timestamp;
    let signature = BASE64_STANDARD
        .decode(sig_base64)
        .map_err(|_| anyhow::anyhow!("failed to base64-decode Rekor signature"))?;
    Ok(signature)
}

#[cfg(test)]
mod tests;
