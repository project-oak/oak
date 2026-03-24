//
// Copyright 2026 The Project Oak Authors
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

//! [C2SP signed-note](https://c2sp.org/signed-note) utilities.
//!
//! This module implements the key, signature, and verification types used by
//! the C2SP signed-note specification.  Signature verification supports
//! Ed25519 (type 0x01) and timestamped Ed25519 witness cosignatures (type
//! 0x04) as defined by the
//! [signed-note specification](https://c2sp.org/signed-note#signature-types).

use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
    vec::Vec,
};

use base64::{Engine, engine::general_purpose::STANDARD as B64};
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use oak_digest::Sha256;
use oak_time::Instant;
use thiserror::Error;

/// Constructs the signed payload for a
/// [C2SP cosignature/v1](https://c2sp.org/tlog-cosignature).
fn cosignature_payload(timestamp_secs: u64, checkpoint_text: &str) -> String {
    format!("cosignature/v1\ntime {}\n{}", timestamp_secs, checkpoint_text)
}

/// Errors produced when parsing or verifying note-format keys and signatures.
#[derive(Error, Debug)]
pub enum NoteError {
    #[error("malformed signature")]
    MalformedSignature,
    #[error("malformed verifying key")]
    MalformedVerifyingKey,
    #[error("signature verification failed")]
    SignatureVerificationFailed,
    #[error("malformed data")]
    Format(#[from] Box<dyn core::error::Error + Send + Sync>),
}

/// Signature type identifier as defined by the
/// [C2SP signed-note specification](https://c2sp.org/signed-note#signature-types).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureType {
    /// 0x01 — Ed25519 (RFC 8032) signature over the note text.
    Ed25519,
    /// 0x04 — Timestamped Ed25519 witness cosignature
    /// ([c2sp.org/tlog-cosignature](https://c2sp.org/tlog-cosignature)).
    CosignatureV1,
}

impl SignatureType {
    /// Returns the C2SP signature-type identifier byte.
    pub fn as_byte(self) -> u8 {
        match self {
            SignatureType::Ed25519 => 0x01,
            SignatureType::CosignatureV1 => 0x04,
        }
    }

    pub(crate) fn from_byte(b: u8) -> Result<Self, NoteError> {
        match b {
            0x01 => Ok(SignatureType::Ed25519),
            0x04 => Ok(SignatureType::CosignatureV1),
            _ => Err(NoteError::MalformedVerifyingKey),
        }
    }
}

/// A signing key in note format, bundled with its derived
/// [`NoteVerifyingKey`] for convenient identity access.
///
/// Supports producing both Ed25519 (type 0x01) and timestamped
/// cosignature (type 0x04) note signatures.
#[derive(Debug, Clone)]
pub struct NoteSigningKey {
    pub signing_key: SigningKey,
    pub verifying_key: NoteVerifyingKey,
}

impl NoteSigningKey {
    /// Creates a new `NoteSigningKey` from its constituent parts.
    ///
    /// The corresponding [`NoteVerifyingKey`] is derived automatically.
    pub fn from_parts(origin: &str, signature_type: SignatureType, raw: [u8; 32]) -> Self {
        let signing_key = SigningKey::from_bytes(&raw);
        let verifying_key =
            NoteVerifyingKey::from_parts(origin, signature_type, signing_key.verifying_key());
        Self { signing_key, verifying_key }
    }

    /// Produces a [`NoteSignature`] over the given checkpoint text,
    /// dispatching based on the key's [`SignatureType`].
    ///
    /// For [`SignatureType::Ed25519`] (type 0x01), signs the checkpoint text
    /// directly and `timestamp` is ignored.
    ///
    /// For [`SignatureType::CosignatureV1`] (type 0x04), signs
    /// `"cosignature/v1\ntime <ts>\n<checkpoint>"` and the signature bytes
    /// are `<8-byte-BE-timestamp> || <ed25519-sig>`.
    pub fn sign(&self, checkpoint_text: &str, timestamp: Instant) -> NoteSignature {
        match self.verifying_key.signature_type {
            SignatureType::Ed25519 => {
                let signature = self.signing_key.sign(checkpoint_text.as_bytes());
                NoteSignature {
                    origin: self.verifying_key.origin.clone(),
                    key_id_hint: self.verifying_key.key_id_hint,
                    sig_bytes: signature.to_bytes().to_vec(),
                }
            }
            SignatureType::CosignatureV1 => {
                let epoch_secs = timestamp.into_unix_seconds() as u64;
                let payload = cosignature_payload(epoch_secs, checkpoint_text);
                let signature = self.signing_key.sign(payload.as_bytes());
                let mut sig_bytes = Vec::new();
                sig_bytes.extend_from_slice(&epoch_secs.to_be_bytes());
                sig_bytes.extend_from_slice(&signature.to_bytes());
                NoteSignature {
                    origin: self.verifying_key.origin.clone(),
                    key_id_hint: self.verifying_key.key_id_hint,
                    sig_bytes,
                }
            }
        }
    }
}

/// A verifying key for a checkpoint signature in note format.
///
/// Supports Ed25519 signatures (type 0x01) and timestamped Ed25519 witness
/// cosignatures (type 0x04) as defined by the
/// [C2SP signed-note specification](https://c2sp.org/signed-note).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoteVerifyingKey {
    pub origin: String,
    pub key_id_hint: [u8; 4],
    pub signature_type: SignatureType,
    pub verifying_key: VerifyingKey,
}

impl NoteVerifyingKey {
    /// Creates a new `NoteVerifyingKey` from its constituent parts.
    pub fn from_parts(
        origin: &str,
        signature_type: SignatureType,
        verifying_key: VerifyingKey,
    ) -> Self {
        let raw = verifying_key.to_bytes();
        let mut data = Vec::with_capacity(origin.len() + 2 + raw.len());
        data.extend_from_slice(origin.as_bytes());
        data.push(b'\n');
        data.push(signature_type.as_byte());
        data.extend_from_slice(&raw);
        let hash: [u8; 32] = Sha256::from_contents(&data).into();
        let key_id_hint: [u8; 4] = hash[..4].try_into().unwrap();
        Self { origin: origin.to_string(), key_id_hint, signature_type, verifying_key }
    }

    /// Parses a verifying key in note format.
    ///
    /// The format is `<key name>+<hex key ID>+<base64(signature type || public
    /// key)>`.
    ///
    /// Valid example input:
    /// ```text
    /// paic.google.com/log/0+609b8245+Ae74NkuIVBowBYu37xUJ5e3wf52bMPhW9e59idWfWR2j
    /// ```
    pub fn parse(serialized: &str) -> Result<Self, NoteError> {
        // There may be more plusses in the base64 encoded part.
        let parts: Vec<&str> = serialized.splitn(3, '+').collect();
        if parts.len() < 3 {
            return Err(NoteError::MalformedVerifyingKey);
        }
        let origin = parts[0].to_string();
        let id_encoded = parts[1];
        let key_encoded = parts[2];
        let id_bytes = hex::decode(id_encoded).map_err(|_| NoteError::MalformedVerifyingKey)?;
        let key_bytes = B64.decode(key_encoded).map_err(|_| NoteError::MalformedVerifyingKey)?;
        if key_bytes.len() != 33 {
            return Err(NoteError::MalformedVerifyingKey);
        }
        let signature_type = SignatureType::from_byte(key_bytes[0])?;
        let key_id_hint: [u8; 4] =
            id_bytes.as_slice().try_into().map_err(|_| NoteError::MalformedVerifyingKey)?;
        let raw: [u8; 32] =
            key_bytes[1..33].try_into().map_err(|_| NoteError::MalformedVerifyingKey)?;
        let verifying_key =
            VerifyingKey::from_bytes(&raw).map_err(|_| NoteError::MalformedVerifyingKey)?;
        Ok(NoteVerifyingKey { origin, key_id_hint, signature_type, verifying_key })
    }

    /// Serialises this verifying key back to note vkey string format:
    /// `<origin>+<hex key ID>+<base64(signature type || public key)>`.
    pub fn to_vkey_string(&self) -> String {
        let mut key_material = alloc::vec![self.signature_type.as_byte()];
        key_material.extend_from_slice(&self.verifying_key.to_bytes());
        format!("{}+{}+{}", self.origin, hex::encode(self.key_id_hint), B64.encode(&key_material))
    }

    /// Verifies that `sig` is a valid signature over the given checkpoint text
    /// using this key, handling signature-type-specific payload framing.
    pub fn verify(&self, checkpoint_text: &str, sig: &NoteSignature) -> Result<(), NoteError> {
        match self.signature_type {
            SignatureType::Ed25519 => {
                if sig.sig_bytes.len() != 64 {
                    return Err(NoteError::MalformedSignature);
                }
                self.verify_ed25519(checkpoint_text.as_bytes(), &sig.sig_bytes)
            }
            SignatureType::CosignatureV1 => {
                if sig.sig_bytes.len() != 72 {
                    return Err(NoteError::MalformedSignature);
                }
                let timestamp = u64::from_be_bytes(sig.sig_bytes[0..8].try_into().unwrap());
                let payload = cosignature_payload(timestamp, checkpoint_text);
                self.verify_ed25519(payload.as_bytes(), &sig.sig_bytes[8..72])
            }
        }
    }

    /// Performs raw Ed25519 signature verification.
    fn verify_ed25519(&self, message: &[u8], signature: &[u8]) -> Result<(), NoteError> {
        let sig =
            Signature::from_bytes(signature.try_into().map_err(|_| NoteError::MalformedSignature)?);
        self.verifying_key
            .verify(message, &sig)
            .map_err(|_| NoteError::SignatureVerificationFailed)?;
        Ok(())
    }
}

/// A signature on a checkpoint in note format.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoteSignature {
    pub origin: String,
    pub key_id_hint: [u8; 4],
    pub sig_bytes: Vec<u8>,
}

impl NoteSignature {
    /// Parses a signature line from a C2SP t-log proof.
    ///
    /// Valid example input:
    /// ```text
    /// — paic.google.com/log/0 YJuCRffzjw85Wjrgi2alFJT94ZC97L+PYMnBPs4q/pN8y/h5Q3lyUfILQCS7bA6xgc/1CaX+T/yRXNhIIJbqvsjR4wU=
    /// ```
    pub fn parse(serialized: &str) -> Result<NoteSignature, NoteError> {
        let strip = serialized.strip_prefix("— ").ok_or(NoteError::MalformedSignature)?;
        let (origin, encoded) = strip.split_once(' ').ok_or(NoteError::MalformedSignature)?;
        let b = B64.decode(encoded).map_err(|e| NoteError::Format(Box::new(e)))?;
        if b.len() < 4 {
            return Err(NoteError::MalformedSignature);
        }
        Ok(NoteSignature {
            origin: origin.to_string(),
            key_id_hint: b[0..4].try_into().unwrap(),
            sig_bytes: b[4..].to_vec(),
        })
    }

    /// Returns `true` if this signature's origin and key ID hint match the
    /// given verifying key, i.e. this signature *could* have been produced
    /// by that key.
    pub fn matches_key(&self, vkey: &NoteVerifyingKey) -> bool {
        self.origin == vkey.origin && self.key_id_hint == vkey.key_id_hint
    }

    /// Serialises this signature to its wire-format line:
    /// `— <origin> <base64(key_id_hint || sig_bytes)>`.
    pub fn to_signature_line(&self) -> String {
        let mut payload = Vec::new();
        payload.extend_from_slice(&self.key_id_hint);
        payload.extend_from_slice(&self.sig_bytes);
        format!("— {} {}", self.origin, B64.encode(&payload))
    }
}

#[cfg(test)]
mod tests {
    use base64::{Engine, engine::general_purpose::STANDARD as B64};

    use super::*;

    #[test]
    fn test_parse_signature_missing_prefix() {
        assert!(matches!(NoteSignature::parse("origin sig"), Err(NoteError::MalformedSignature)));
    }

    #[test]
    fn test_parse_signature_invalid_base64() {
        assert!(matches!(NoteSignature::parse("— origin @@@@"), Err(NoteError::Format(_))));
    }

    #[test]
    fn test_parse_signature_too_short() {
        // "AAAA" decodes to 3 bytes, below the 4-byte key ID minimum.
        assert!(matches!(
            NoteSignature::parse("— origin AAAA"),
            Err(NoteError::MalformedSignature)
        ));
    }

    #[test]
    fn test_parse_verifying_key_too_few_parts() {
        assert!(matches!(
            NoteVerifyingKey::parse("origin+id"),
            Err(NoteError::MalformedVerifyingKey)
        ));
    }

    #[test]
    fn test_parse_verifying_key_unsupported_version() {
        let mut key_bytes = [0u8; 33];
        key_bytes[0] = 0x02; // unsupported version
        let key_b64 = B64.encode(key_bytes);
        let serialized = format!("origin+12345678+{}", key_b64);
        assert!(matches!(
            NoteVerifyingKey::parse(&serialized),
            Err(NoteError::MalformedVerifyingKey)
        ));
    }

    #[test]
    fn test_parse_verifying_key_wrong_length() {
        let key_bytes = [0u8; 30]; // too short
        let key_b64 = B64.encode(key_bytes);
        let serialized = format!("origin+12345678+{}", key_b64);
        assert!(matches!(
            NoteVerifyingKey::parse(&serialized),
            Err(NoteError::MalformedVerifyingKey)
        ));
    }

    #[test]
    fn test_verify_ed25519_wrong_key() {
        let signer =
            NoteSigningKey::from_parts("example.com/log", SignatureType::Ed25519, [42u8; 32]);
        let other =
            NoteSigningKey::from_parts("example.com/log", SignatureType::Ed25519, [99u8; 32]);
        let signed_text = "test message\n";
        let sig = signer.sign(signed_text, Instant::UNIX_EPOCH);

        let result = other.verifying_key.verify(signed_text, &sig);
        assert!(matches!(result, Err(NoteError::SignatureVerificationFailed)));
    }

    #[test]
    fn test_roundtrip_vkey_string() {
        let key = NoteSigningKey::from_parts("example.com/log", SignatureType::Ed25519, [42u8; 32]);
        let vkey_str = key.verifying_key.to_vkey_string();
        let parsed = NoteVerifyingKey::parse(&vkey_str).unwrap();
        assert_eq!(key.verifying_key, parsed);
    }

    #[test]
    fn test_roundtrip_signature_line() {
        let key = NoteSigningKey::from_parts("example.com/log", SignatureType::Ed25519, [42u8; 32]);
        let sig = key.sign("test payload\n", Instant::UNIX_EPOCH);
        let line = sig.to_signature_line();
        let parsed = NoteSignature::parse(&line).unwrap();
        assert_eq!(sig.origin, parsed.origin);
        assert_eq!(sig.key_id_hint, parsed.key_id_hint);
        assert_eq!(sig.sig_bytes, parsed.sig_bytes);
    }

    #[test]
    fn test_cosignature_roundtrip() {
        let key = NoteSigningKey::from_parts(
            "witness.example.com",
            SignatureType::CosignatureV1,
            [43u8; 32],
        );
        let checkpoint = "example.com/log\n42\nhash\n";
        let sig = key.sign(checkpoint, Instant::from_unix_seconds(1700000000));
        assert!(key.verifying_key.verify(checkpoint, &sig).is_ok());
    }

    #[test]
    fn test_matches_key() {
        let key = NoteSigningKey::from_parts("example.com/log", SignatureType::Ed25519, [42u8; 32]);
        let sig = key.sign("test\n", Instant::UNIX_EPOCH);
        assert!(sig.matches_key(&key.verifying_key));

        let other = NoteSigningKey::from_parts("other.com/log", SignatureType::Ed25519, [99u8; 32]);
        assert!(!sig.matches_key(&other.verifying_key));
    }
}
