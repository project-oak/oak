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

pub mod hashedrekord;

use alloc::{string::String, vec::Vec};
use core::str::FromStr;

use base64::{prelude::BASE64_STANDARD, Engine};
use p256::ecdsa::{signature::Verifier, Signature, VerifyingKey};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_json::Value;

use crate::error::Error;

#[derive(thiserror::Error, Debug)]
pub enum RekorError {
    #[error("Malformed bundle")]
    MalformedBundle,
}

/// Represents the payload of a Rekor entry.
///
/// This struct contains the fields from a `LogEntry` that are signed to create
/// the inclusion promise. For more details about all the fields in `LogEntry`
/// and the verification process, see the `LogEntry` definition in
/// the [Rekor OpenAPI specification](https://github.com/sigstore/rekor/blob/d920fad17c98aff21d98036db6a4820542f7d18d/openapi.yaml#L446-L488).
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct RekorPayload {
    /// Base64-encoded content of the Rekor entry.
    pub body: String,
    /// The timestamp when this entry was added to the log, in seconds since the
    /// Unix Epoch.
    #[serde(rename = "integratedTime")]
    pub integrated_time: i64,
    /// The SHA256 hash of the DER-encoded public key for the log at the time
    /// the entry was included.
    #[serde(rename = "logID")]
    pub log_id: String,
    /// The serial number of the entry in the log.
    #[serde(rename = "logIndex")]
    pub log_index: i64,
}

/// Represents a Rekor bundle that has not yet been verified.
#[derive(Debug, PartialEq)]
pub struct Unverified {
    signature: Vec<u8>,
}

/// Represents a Rekor bundle that has been successfully verified.
#[derive(Debug, PartialEq)]
pub struct Verified;

/// Represents a Rekor bundle, which contains a payload and a signature.
///
/// The `S` type parameter represents the verification state of the bundle.
#[derive(Debug, PartialEq)]
pub struct RekorBundle<S> {
    payload: RekorPayload,
    signature: S,
}

impl RekorBundle<Unverified> {
    /// Verifies the Rekor inclusion promise bundle.
    ///
    /// This implementation follows the specification in
    /// https://docs.sigstore.dev/cosign/verifying/verify/#verify-a-signature-was-added-to-the-transparency-log
    pub fn verify(self, rekor_public_key: &VerifyingKey) -> Result<RekorBundle<Verified>, Error> {
        let signature =
            Signature::from_der(&self.signature.signature).map_err(Error::SignatureDer)?;
        // As per the spec above, the signature of the payload is done over the
        // Canonicalized representation of these fields:
        // * No whitespace
        // * JSON keys are sorted lexicographically
        // Because serde_json's Value uses a BTreeMap, the sorting property holds for
        // object values.
        let message = serde_json::json!({
            "body": self.payload.body.clone(),
            "integratedTime": self.payload.integrated_time,
            "logID": self.payload.log_id.clone(),
            "logIndex": self.payload.log_index.clone(),
        });
        let message = serde_json::to_string(&message)?;
        rekor_public_key.verify(message.as_bytes(), &signature).map_err(Error::Verification)?;

        Ok(RekorBundle { payload: self.payload, signature: Verified })
    }
}

impl RekorBundle<Verified> {
    /// Deserializes the base64-encoded body of the Rekor payload into a
    /// specific type.
    pub fn payload_body<T: DeserializeOwned>(&self) -> Result<T, Error> {
        let body = BASE64_STANDARD.decode(&self.payload.body)?;
        serde_json::from_slice(&body).map_err(Error::Json)
    }
}

impl FromStr for RekorBundle<Unverified> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let bundle: Value = serde_json::from_str(s)?;
        let payload = bundle.get("Payload").ok_or(RekorError::MalformedBundle)?;
        let payload: RekorPayload = RekorPayload::deserialize(payload)?;
        let signature = bundle.get("SignedEntryTimestamp").ok_or(RekorError::MalformedBundle)?;
        let signature: String = String::deserialize(signature)?;
        let signature: Vec<u8> = BASE64_STANDARD.decode(signature)?;

        Ok(Self { payload, signature: Unverified { signature } })
    }
}

#[cfg(test)]
mod tests {
    use core::assert_matches::assert_matches;

    use p256::ecdsa::{
        signature::{SignatureEncoding, Signer},
        SigningKey,
    };
    use serde_json::json;

    use super::*;

    const SIGNING_KEY_BYTES: [u8; 32] = [
        0xad, 0x57, 0x5f, 0x38, 0x17, 0x7e, 0x11, 0x4a, 0x48, 0x2d, 0x5a, 0x24, 0x71, 0x28, 0x73,
        0x64, 0x27, 0x41, 0x53, 0x48, 0x51, 0x5b, 0x76, 0x78, 0x47, 0x11, 0x12, 0x43, 0x01, 0x61,
        0x64, 0x66,
    ];

    const ANOTHER_KEY_BYTES: [u8; 32] = [
        0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0b, 0xed, 0xce, 0xbd, 0x07, 0x60,
        0x1c, 0xc5, 0x79, 0x5c, 0x08, 0x25, 0x87, 0x24, 0x56, 0x20, 0x84, 0x0c, 0x82, 0x94, 0x04,
        0x48, 0x88,
    ];

    #[test]
    fn test_verify_payload_ok() -> anyhow::Result<()> {
        let signing_key =
            SigningKey::from_slice(&SIGNING_KEY_BYTES).map_err(|e| anyhow::anyhow!(e))?;
        let verifying_key = signing_key.verifying_key();

        let payload = json!({
            "body": "bar",
            "integratedTime": 1234,
            "logID": "log_id",
            "logIndex": 5678,
        });
        let signature: Signature = serde_json::to_vec(&payload).map(|s| signing_key.sign(&s))?;

        let bundle = RekorBundle {
            signature: Unverified { signature: signature.to_der().to_vec() },
            payload: serde_json::from_value(payload)?,
        };

        bundle.verify(verifying_key)?;

        Ok(())
    }

    #[test]
    fn test_verify_payload_failed() -> anyhow::Result<()> {
        let signing_key =
            SigningKey::from_slice(&SIGNING_KEY_BYTES).map_err(|e| anyhow::anyhow!(e))?;

        let payload = json!({
            "body": "bar",
            "integratedTime": 1234,
            "logID": "log_id",
            "logIndex": 5678,
        });
        let signature: Signature = serde_json::to_vec(&payload).map(|s| signing_key.sign(&s))?;

        let bundle = RekorBundle {
            signature: Unverified { signature: signature.to_der().to_vec() },
            payload: serde_json::from_value(payload)?,
        };

        // Use the verifying key of a different signing key
        let verifying_key =
            SigningKey::from_slice(&ANOTHER_KEY_BYTES).map_err(|e| anyhow::anyhow!(e))?;
        let verifying_key = verifying_key.verifying_key();

        assert_matches!(bundle.verify(verifying_key), Err(Error::Verification(_)));

        Ok(())
    }
}
