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

use base64::{prelude::BASE64_STANDARD, Engine};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_json::Value;

use crate::{
    error::Error,
    message::{SignedMessage, Unverified},
};

pub const REKOR_PUBLIC_KEY_PEM: &str = include_str!("../data/rekor_public_key.pem");

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

impl RekorPayload {
    /// Deserializes the base64-encoded body of the Rekor payload into a
    /// specific type.
    pub fn payload_body<T: DeserializeOwned>(&self) -> Result<T, Error> {
        let body = BASE64_STANDARD.decode(&self.body)?;
        serde_json::from_slice(&body).map_err(Error::Json)
    }
}

pub const LOG_ENTRY_PAYLOAD_KEY: &str = "Payload";
pub const LOG_ENTRY_SIGNATURE_KEY: &str = "SignedEntryTimestamp";

pub fn from_cosign_bundle<T: AsRef<[u8]>>(bundle: T) -> Result<SignedMessage<Unverified>, Error> {
    let bundle: Value = serde_json::from_slice(bundle.as_ref())?;

    let payload = bundle.get(LOG_ENTRY_PAYLOAD_KEY).ok_or(RekorError::MalformedBundle)?;

    // As per the spec above, the signature of the payload is done over the
    // Canonicalized representation of its fields, which means:
    // * No whitespace
    // * JSON keys are sorted lexicographically
    // Because serde_json's Value uses a BTreeMap, the sorting property holds for
    // object values.
    let message = serde_json::to_string(&payload)?;

    let signature = bundle.get(LOG_ENTRY_SIGNATURE_KEY).ok_or(RekorError::MalformedBundle)?;
    let signature: String = String::deserialize(signature)?;
    let signature: Vec<u8> = BASE64_STANDARD.decode(signature)?;

    Ok(SignedMessage::unverified(message.into(), signature))
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;
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

    #[test]
    fn test_rekor_payload_body_deserialization() {
        let payload_body = json!({ "key": "value" });
        let payload_body_str = serde_json::to_string(&payload_body).unwrap();
        let encoded_body = BASE64_STANDARD.encode(payload_body_str);

        let rekor_payload = RekorPayload {
            body: encoded_body,
            integrated_time: 12345,
            log_id: "log_id".to_string(),
            log_index: 1,
        };

        #[derive(Deserialize, PartialEq, Debug)]
        struct TestPayload {
            key: String,
        }

        let deserialized: TestPayload = rekor_payload.payload_body().unwrap();
        assert_eq!(deserialized, TestPayload { key: "value".to_string() });
    }

    #[test]
    fn test_rekor_payload_body_invalid_base64() {
        let rekor_payload = RekorPayload {
            body: "invalid-base64".to_string(),
            integrated_time: 12345,
            log_id: "log_id".to_string(),
            log_index: 1,
        };

        #[derive(Deserialize, PartialEq, Debug)]
        struct TestPayload {
            key: String,
        }

        let result: Result<TestPayload, _> = rekor_payload.payload_body();
        assert_matches!(result, Err(Error::Base64(_)));
    }

    #[test]
    fn test_rekor_payload_body_invalid_json() {
        let encoded_body = BASE64_STANDARD.encode("not a json");
        let rekor_payload = RekorPayload {
            body: encoded_body,
            integrated_time: 12345,
            log_id: "log_id".to_string(),
            log_index: 1,
        };

        #[derive(Deserialize, PartialEq, Debug)]
        struct TestPayload {
            key: String,
        }

        let result: Result<TestPayload, _> = rekor_payload.payload_body();
        assert_matches!(result, Err(Error::Json(_)));
    }

    #[test]
    fn test_from_cosign_bundle_success() {
        let payload = json!({
            "body": "c29tZSBib2R5",
            "integratedTime": 123,
            "logID": "log_id",
            "logIndex": 456,
        });
        let message = serde_json::to_vec(&payload).unwrap();

        let signing_key = SigningKey::from_bytes(&SIGNING_KEY_BYTES.into()).unwrap();
        let signature: p256::ecdsa::Signature = signing_key.sign(&message);
        let signature_b64 = BASE64_STANDARD.encode(signature.to_der());

        let bundle = json!({
            "Payload": payload,
            "SignedEntryTimestamp": signature_b64,
        });
        let bundle_str = serde_json::to_string(&bundle).unwrap();

        let signed_message = from_cosign_bundle(&bundle_str).unwrap();

        assert_eq!(signed_message, SignedMessage::unverified(message, signature.to_der().to_vec()));
    }

    #[test]
    fn test_from_cosign_bundle_missing_payload() {
        let bundle = json!({
            "SignedEntryTimestamp": "signature",
        });
        let bundle_str = serde_json::to_string(&bundle).unwrap();
        let result = from_cosign_bundle(&bundle_str);
        assert_matches!(result, Err(Error::Rekor(RekorError::MalformedBundle)));
    }

    #[test]
    fn test_from_cosign_bundle_missing_signature() {
        let payload = json!({
            "body": "c29tZSBib2R5",
        });
        let bundle = json!({
            "Payload": payload,
        });
        let bundle_str = serde_json::to_string(&bundle).unwrap();
        let result = from_cosign_bundle(&bundle_str);
        assert_matches!(result, Err(Error::Rekor(RekorError::MalformedBundle)));
    }

    #[test]
    fn test_from_cosign_bundle_invalid_signature_base64() {
        let payload = json!({
            "body": "c29tZSBib2R5",
        });
        let bundle = json!({
            "Payload": payload,
            "SignedEntryTimestamp": "invalid-base64",
        });
        let bundle_str = serde_json::to_string(&bundle).unwrap();
        let result = from_cosign_bundle(&bundle_str);
        assert_matches!(result, Err(Error::Base64(_)));
    }
}
