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

//! This module provides functionality for fetching and verifying cosign
//! signatures from an OCI registry.

use alloc::vec::Vec;

use p256::ecdsa::{signature::Verifier, Signature, VerifyingKey};
use serde::de::DeserializeOwned;

use crate::error::Error;

/// Represents a cosign payload that has not yet been verified.
#[derive(Debug)]
pub struct Unverified {
    data: Vec<u8>,
    // Signature in binary DER encoding.
    signature: Vec<u8>,
}

/// Represents a cosign payload that has been successfully verified.
#[derive(Debug)]
pub struct Verified {
    data: Vec<u8>,
}

/// A bundle containing a payload and its associated signature information.
///
/// The `P` type parameter represents the verification state of the payload.
#[derive(Debug)]
pub struct SignatureBundle<P> {
    pub payload: P,
}

impl SignatureBundle<Unverified> {
    pub fn new(data: Vec<u8>, signature: Vec<u8>) -> Self {
        Self { payload: Unverified { data, signature } }
    }

    /// Verifies the signature of the payload.
    ///
    /// On success, returns a `SignatureBundle` with a verified payload.
    pub fn verify(self, verifier: &VerifyingKey) -> Result<SignatureBundle<Verified>, Error> {
        let signature =
            Signature::from_der(&self.payload.signature).map_err(Error::SignatureDer)?;
        verifier.verify(&self.payload.data, &signature).map_err(Error::Verification)?;

        Ok(SignatureBundle { payload: Verified { data: self.payload.data } })
    }
}

impl SignatureBundle<Verified> {
    /// Returns the raw data of the verified payload.
    pub fn data(&self) -> &[u8] {
        &self.payload.data
    }

    /// Deserializes the payload data into a specific type.
    pub fn data_payload<P: DeserializeOwned>(&self) -> Result<P, serde_json::Error> {
        serde_json::from_slice(&self.payload.data)
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
    fn test_verify() -> anyhow::Result<()> {
        let signing_key =
            SigningKey::from_slice(&SIGNING_KEY_BYTES).map_err(|e| anyhow::anyhow!(e))?;
        let verifying_key = signing_key.verifying_key();

        let data = br#"{"foo":"bar"}"#;
        let signature: Signature = signing_key.sign(data);

        let payload = SignatureBundle {
            payload: Unverified { data: data.to_vec(), signature: signature.to_der().to_vec() },
        };

        let payload: SignatureBundle<Verified> = payload.verify(verifying_key)?;

        assert_eq!(payload.data(), br#"{"foo":"bar"}"#);
        assert_eq!(payload.data_payload::<serde_json::Value>()?, json!({"foo":"bar"}));

        Ok(())
    }

    #[test]
    fn test_verify_fails() -> anyhow::Result<()> {
        let signing_key =
            SigningKey::from_slice(&SIGNING_KEY_BYTES).map_err(|e| anyhow::anyhow!(e))?;
        // A different key for verification.
        let verifying_key =
            SigningKey::from_slice(&ANOTHER_KEY_BYTES).map_err(|e| anyhow::anyhow!(e))?;
        let verifying_key = verifying_key.verifying_key();

        let data = br#"{"foo":"bar"}"#.to_vec();
        let signature: Signature = signing_key.sign(&data);

        let payload = SignatureBundle {
            payload: Unverified { data, signature: signature.to_der().to_vec() },
        };

        let result = payload.verify(verifying_key);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_matches!(err, Error::Verification(_));

        Ok(())
    }
}
