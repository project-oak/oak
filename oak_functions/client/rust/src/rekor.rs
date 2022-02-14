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

use anyhow::Context;
use ecdsa::Signature;
use serde::{Deserialize, Serialize};
use signature::Verifier;
use std::str::FromStr;

/// Struct representing a Rekor LogEntry.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct LogEntry {
    #[serde(rename = "body")]
    pub body: String,

    #[serde(rename = "integratedTime")]
    pub integrated_time: usize,

    // TODO(#2316): should this be verified?
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

    /// Signature over the canonicalized JSON document. This is obtained by decoding the
    /// Base64-encoded `signedEntryTimestamp` in the Rekor LogEntry.
    pub signature: p256::ecdsa::Signature,
}

/// Convertor for creating a RekorSignatureBundle from a Rekor LogEntry as described in https://github.com/sigstore/rekor/blob/4fcdcaa58fd5263560a82978d781eb64f5c5f93c/openapi.yaml#L433-L476.
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
            .ok_or(anyhow::anyhow!("no verification field in the log entry"))?
            .signed_entry_timestamp
            .clone();
        let sig_bytes = sig_base64.as_str().as_bytes();
        let sig =
            base64::decode(sig_bytes).context("couldn't decode Base64 signedEntryTimestamp")?;
        let signature = Signature::from_der(&sig).context("invalid ASN.1 signature")?;

        Ok(Self {
            canonicalized,
            signature,
        })
    }
}

/// Verifies a Rekor LogEntry.
///
/// The verification involves the following:
///
/// 1. verifying the signature in `signedEntryTimestamp`, using Rekor's public key,
/// 1. verifying the signature in `body.RekordObj.signature`, using Oak's public key,
/// 1. verifying that the content of the body matches the input `endorsement_bytes`.
///
/// Returns `Ok(())` if the verification succeeds, otherwise returns `Err()`.
pub fn verify_rekor_log_entry(
    log_entry_bytes: &[u8],
    pem_encoded_public_key_bytes: &[u8],
    _oak_public_key_bytes: &[u8],
    _endorsement_bytes: &[u8],
) -> anyhow::Result<()> {
    verify_rekor_signature(log_entry_bytes, pem_encoded_public_key_bytes)?;

    let parsed: std::collections::HashMap<String, LogEntry> =
        serde_json::from_slice(log_entry_bytes)
            .context("couldn't parse bytes into a LogEntry object.")?;
    let _entry = parsed.values().next().context("no entry in the map")?;
    // TODO(#2316): entry.body is base64 encoded. It should be decoded to extract content and
    // signature from it.

    // TODO(#2316): verify signature in the body using oak's public key

    // TODO(#2316): check that the endorsement has the same hash as the one in the body.

    Ok(())
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
    pem_encoded_public_key_bytes: &[u8],
) -> anyhow::Result<()> {
    let signature_bundle = rekor_signature_bundle(log_entry_bytes)?;
    let key = unmarshal_pem_to_p256_public_key(pem_encoded_public_key_bytes)?;

    key.verify(&signature_bundle.canonicalized, &signature_bundle.signature)
        .context("failed to verify signedEntryTimestamp of the Rekor LogEntry")
}

/// Parses a PEM-encoded x509/PKIX public key into a `p256::ecdsa::VerifyingKey`.
///
/// `pem_bytes`: A PEM-encoded public key as a byte array.
pub fn unmarshal_pem_to_p256_public_key(
    pem_bytes: &[u8],
) -> anyhow::Result<p256::ecdsa::VerifyingKey> {
    let pem_str = std::str::from_utf8(pem_bytes).context("couldn't convert bytes to string")?;
    p256::ecdsa::VerifyingKey::from_str(pem_str)
        .context("couldn't parse pem as a p256::ecdsa::VerifyingKey")
}

fn rekor_signature_bundle(log_entry_bytes: &[u8]) -> anyhow::Result<RekorSignatureBundle> {
    let parsed: std::collections::HashMap<String, LogEntry> =
        serde_json::from_slice(log_entry_bytes)
            .context("couldn't parse bytes into a LogEntry object.")?;
    let entry = parsed.values().next().context("no entry in the map")?;

    RekorSignatureBundle::try_from(entry)
}
