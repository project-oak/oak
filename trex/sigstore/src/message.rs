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

use alloc::vec::Vec;

use p256::ecdsa::{signature::Verifier, VerifyingKey};

use crate::error;

/// Represents a signed message that is entirely raw and the message and
/// signature have not yet been separated.
#[derive(Debug, PartialEq)]
pub struct Raw {
    // Raw message
    data: Vec<u8>,
}

/// Represents a signed message that has not yet been verified.
#[derive(Debug, PartialEq)]
pub struct Unverified {
    // Raw unverified message
    message: Vec<u8>,
    // Signature in binary DER encoding.
    signature: Vec<u8>,
}

/// Represents a signed message that has been successfully verified.
#[derive(Debug, PartialEq)]
pub struct Verified {
    // Raw, but verified, message
    message: Vec<u8>,
}

/// A bundle represending a signed message and its verification state.
///
/// The `S` type parameter represents the verification state of the message.
#[derive(Debug, PartialEq)]
pub struct SignedMessage<S> {
    pub state: S,
}

impl SignedMessage<Raw> {
    /// Create a new raw message.
    pub fn raw(data: Vec<u8>) -> Self {
        Self { state: Raw { data } }
    }

    pub fn raw_data(&self) -> &[u8] {
        &self.state.data
    }
}

impl AsRef<[u8]> for SignedMessage<Raw> {
    fn as_ref(&self) -> &[u8] {
        self.raw_data()
    }
}

impl SignedMessage<Unverified> {
    /// Create a new unverified message from its content and its signature
    pub fn unverified(message: Vec<u8>, signature: Vec<u8>) -> Self {
        Self { state: Unverified { message, signature } }
    }

    /// Verifies the signature of the payload.
    ///
    /// On success, returns a `SignatureBundle` with a verified payload.
    pub fn verify(self, verifier: &VerifyingKey) -> Result<SignedMessage<Verified>, error::Error> {
        let signature = p256::ecdsa::Signature::from_der(&self.state.signature)
            .map_err(error::Error::SignatureDer)?;

        verifier
            .verify(&self.state.message, &signature)
            .map_err(error::Error::SignatureVerification)?;

        Ok(SignedMessage::verified(self.state.message))
    }

    /// Obtains a reference to the unverified message.
    pub fn unverified_message(&self) -> &[u8] {
        &self.state.message
    }

    /// Extracts the unverified signature.
    pub fn signature(&self) -> &[u8] {
        &self.state.signature
    }
}

impl SignedMessage<Verified> {
    /// Creates a verified message. Internal only.
    fn verified(message: Vec<u8>) -> Self {
        Self { state: Verified { message } }
    }

    /// Returns the raw verified message.
    pub fn message(&self) -> &[u8] {
        &self.state.message
    }
}

impl AsRef<[u8]> for SignedMessage<Verified> {
    fn as_ref(&self) -> &[u8] {
        self.message()
    }
}

#[cfg(test)]
mod tests {
    use core::assert_matches::assert_matches;

    use p256::ecdsa::{
        signature::{SignatureEncoding, Signer},
        Signature, SigningKey,
    };

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

        let payload = SignedMessage::unverified(data.to_vec(), signature.to_der().to_vec());

        let payload: SignedMessage<Verified> = payload.verify(verifying_key)?;

        assert_eq!(payload.message(), br#"{"foo":"bar"}"#);

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

        let payload = SignedMessage::unverified(data, signature.to_der().to_vec());

        let result = payload.verify(verifying_key);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_matches!(err, error::Error::SignatureVerification(_));

        Ok(())
    }
}
