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

//! Implements the HashedRekord schema for Rekor.
//! https://github.com/sigstore/rekor/blob/main/pkg/types/hashedrekord/v0.0.1/schema.json

use alloc::string::{String, ToString};

use base64::{prelude::BASE64_STANDARD, Engine};
use p256::{
    ecdsa::{signature::Verifier, Signature, VerifyingKey},
    pkcs8::DecodePublicKey,
};
use serde::{de, Deserialize, Deserializer};
use serde_json::Value;
use sha2::Digest;

use crate::error::Error;

#[derive(thiserror::Error, Debug)]
pub enum HashedRekordError {
    #[error("Unsupported hash algorithm: {0}")]
    UnsupportedHashAlgorithm(String),
    #[error("The hash of the rekord does not match the hash in the HashedRekord body")]
    HashMismatch,
    #[error("Invalid API version: {0}")]
    InvalidApiVersion(String),
    #[error("Invalid Rekor kind: {0}")]
    InvalidRekorKind(String),
    #[error("Public key in rekord did not match verifying key")]
    PublicKeyMismatch,
    #[error("Missing field in JSON: {0}")]
    MissingField(String),
}

/// Represents a HashedRekord entry from Rekor.
///
/// See the [HashedRekord specification](https://github.com/sigstore/rekor/blob/main/pkg/types/hashedrekord/v0.0.1/hashedrekord_v0_0_1_schema.json) for more details.
///
/// The `S` type parameter represents the verification state of the entry.
#[derive(Debug, PartialEq)]
pub struct HashedRekord<S> {
    hash_algorithm: String,
    hash_value: String,
    state: S,
}

/// Represents an unverified HashedRekord.
///
/// This struct holds the signature and public key content that has not yet
/// been verified.
#[derive(Debug, PartialEq)]
pub struct Unverified {
    signature: String,
    public_key: String,
}

/// Represents a HashedRekord that has been successfully verified.
///
/// This struct indicates that the signature in the HashedRekord has been
/// verified against the public key and the Rekor entry data.
#[derive(Debug, PartialEq)]
pub struct Verified;

impl<'de> Deserialize<'de> for HashedRekord<Unverified> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let v = Value::deserialize(deserializer)?;

        if !matches!(v["apiVersion"], Value::String(_)) {
            return Err(de::Error::custom("invalid apiVersion"));
        }

        if !matches!(v["kind"], Value::String(_)) {
            return Err(de::Error::custom("invalid kind"));
        }

        let hash_algorithm = v["spec"]["data"]["hash"]["algorithm"]
            .as_str()
            .ok_or(de::Error::custom("missing spec.data.hash.algorithm"))?;
        let hash_value = v["spec"]["data"]["hash"]["value"]
            .as_str()
            .ok_or(de::Error::custom("missing spec.data.hash.value"))?;
        let signature = v["spec"]["signature"]["content"]
            .as_str()
            .ok_or(de::Error::custom("missing spec.signature.content"))?;
        let public_key = v["spec"]["signature"]["publicKey"]["content"]
            .as_str()
            .ok_or(de::Error::custom("missing spec.signature.publicKey.content"))?;

        Ok(HashedRekord {
            hash_algorithm: hash_algorithm.to_string(),
            hash_value: hash_value.to_string(),
            state: Unverified {
                signature: signature.to_string(),
                public_key: public_key.to_string(),
            },
        })
    }
}

impl HashedRekord<Unverified> {
    /// Verifies the integrity of the HashedRekord.
    ///
    /// This function performs the following checks:
    /// 1. The public key in the HashedRekord matches the provided
    ///    `verifying_key`.
    /// 2. The signature is a valid signature of the `rekord` data verified
    ///    using the public key.
    /// 3. The SHA-256 hash of the `rekord` data matches the hash stored in the
    ///    HashedRekord.
    pub fn verify(
        self,
        verifying_key: &VerifyingKey,
        rekord: &[u8],
    ) -> Result<HashedRekord<Verified>, Error> {
        let public_key = BASE64_STANDARD.decode(&self.state.public_key)?;
        let public_key = VerifyingKey::from_public_key_pem(core::str::from_utf8(&public_key)?)
            .map_err(Error::PublicKeyDecode)?;

        if &public_key != verifying_key {
            return Err(HashedRekordError::PublicKeyMismatch.into());
        }

        let signature = BASE64_STANDARD.decode(&self.state.signature)?;
        let signature = Signature::from_der(&signature).map_err(Error::SignatureDer)?;

        public_key.verify(rekord, &signature).map_err(Error::SignatureVerification)?;

        let rekord_hash = match self.hash_algorithm.as_str() {
            "sha256" => hex::encode(sha2::Sha256::digest(rekord)),
            _ => {
                return Err(HashedRekordError::UnsupportedHashAlgorithm(
                    self.hash_algorithm.clone(),
                )
                .into())
            }
        };

        if rekord_hash != self.hash_value {
            return Err(HashedRekordError::HashMismatch.into());
        }

        Ok(HashedRekord {
            hash_algorithm: self.hash_algorithm,
            hash_value: self.hash_value,
            state: Verified,
        })
    }
}

impl<S> HashedRekord<S> {
    /// Returns the hash algorithm and value from the HashedRekord.
    pub fn hash(&self) -> (&str, &str) {
        (&self.hash_algorithm, &self.hash_value)
    }
}

#[cfg(test)]
mod tests {
    use core::assert_matches::assert_matches;

    use p256::{
        ecdsa::{signature::Signer, SigningKey},
        pkcs8::EncodePublicKey,
    };
    use sha2::Digest;

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

    fn get_test_rekord(
        hash_value: &str,
        signature_content: &str,
        public_key_content: &str,
    ) -> String {
        let value = serde_json::json!({
            "apiVersion": "0.0.1",
            "kind": "hashedrekord",
            "spec": {
                "data": {
                    "hash": {
                        "algorithm": "sha256",
                        "value": hash_value
                    }
                },
                "signature": {
                    "content": signature_content,
                    "publicKey": {
                        "content": public_key_content
                    }
                }
            }
        });
        serde_json::to_string(&value).unwrap()
    }

    #[test]
    fn test_verify_ok() {
        let signing_key = SigningKey::from_slice(&SIGNING_KEY_BYTES).unwrap();
        let verifying_key = signing_key.verifying_key();
        let verifying_key_str = verifying_key.to_public_key_pem(Default::default()).unwrap();
        let verifying_key_str = BASE64_STANDARD.encode(verifying_key_str);

        let payload = b"foo";
        let sha256hash = hex::encode(sha2::Sha256::digest(payload));

        let signature: Signature = signing_key.sign(payload);
        let signature = BASE64_STANDARD.encode(signature.to_der());

        let rekord_json = get_test_rekord(&sha256hash, &signature, &verifying_key_str);
        let rekord: HashedRekord<Unverified> = serde_json::from_str(&rekord_json).unwrap();

        let verified_rekord = rekord.verify(verifying_key, payload).unwrap();
        let hash = verified_rekord.hash();
        assert_eq!(hash, ("sha256", sha256hash.as_str()));
    }

    #[test]
    fn test_invalid_apiversion() {
        let json = r#"{"apiVersion": "0.0.2", "kind": "hashedrekord", "spec": {}}"#;
        let result: Result<HashedRekord<Unverified>, _> = serde_json::from_str(json);
        assert_matches!(result, Err(_));
    }

    #[test]
    fn test_invalid_kind() {
        let json = r#"{"apiVersion": "0.0.1", "kind": "not-hashedrekord", "spec": {}}"#;
        let result: Result<HashedRekord<Unverified>, _> = serde_json::from_str(json);
        assert_matches!(result, Err(_));
    }

    #[test]
    fn test_verify_key_mismatch() {
        let signing_key = SigningKey::from_slice(&SIGNING_KEY_BYTES).unwrap();

        // We are going to sign the hash with `signing_key`, but use a different
        // key in the Rekord body.
        let another_signing_key = SigningKey::from_slice(&ANOTHER_KEY_BYTES).unwrap();
        let verifying_key_in_rekord = another_signing_key.verifying_key();
        let verifying_key_in_rekord_str =
            verifying_key_in_rekord.to_public_key_pem(Default::default()).unwrap();
        let verifying_key_in_rekord_str = BASE64_STANDARD.encode(verifying_key_in_rekord_str);

        let payload = b"foo";
        let sha256hash = hex::encode(sha2::Sha256::digest(payload));

        let signature: Signature = signing_key.sign(payload);
        let signature = BASE64_STANDARD.encode(signature.to_der());

        let rekord_json = get_test_rekord(&sha256hash, &signature, &verifying_key_in_rekord_str);
        let rekord: HashedRekord<Unverified> = serde_json::from_str(&rekord_json).unwrap();

        let result = rekord.verify(verifying_key_in_rekord, payload);
        assert_matches!(result, Err(Error::SignatureVerification(_)));
    }
}
