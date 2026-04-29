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
//! Ed25519 (type 0x01), timestamped Ed25519 witness cosignatures (type
//! 0x04), and timestamped ML-DSA-44 signatures (type 0x06) as defined by
//! the
//! [signed-note specification](https://c2sp.org/signed-note#signature-types)
//! and the
//! [tlog-cosignature specification](https://c2sp.org/tlog-cosignature).

use alloc::{
    format,
    string::{String, ToString},
    vec::Vec,
};

use base64::{Engine, engine::general_purpose::STANDARD as B64};
use ed25519_dalek::{Signature, Signer, Verifier};
#[cfg(feature = "ml_dsa")]
use oak_crypto_tink::ml_dsa_44;
use oak_digest::Sha256;
use oak_time::Instant;
use thiserror::Error;

/// Errors produced when parsing or verifying note-format keys and signatures.
#[derive(Error, Debug)]
pub enum NoteError {
    #[error("malformed signature")]
    MalformedSignature,
    #[error("malformed verifying key")]
    MalformedVerifyingKey,
    #[error(transparent)]
    MalformedCheckpoint(#[from] crate::CheckpointError),
    #[error("signature verification failed")]
    SignatureVerificationFailed,
    #[error("opaque data exceeds 255 bytes")]
    OpaqueDataTooLong,
}

/// C2SP [signature type](https://c2sp.org/signed-note#signature-types)
/// identifier byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureType {
    /// Ed25519 log signature ([RFC 8032](https://www.rfc-editor.org/rfc/rfc8032)).
    Ed25519 = 0x01,
    /// Timestamped Ed25519 witness cosignature
    /// ([c2sp.org/tlog-cosignature](https://c2sp.org/tlog-cosignature)).
    Ed25519CosignatureV1 = 0x04,
    /// Timestamped ML-DSA-44 subtree signature
    /// ([FIPS 204](https://csrc.nist.gov/pubs/fips/204/final),
    /// [c2sp.org/tlog-cosignature](https://c2sp.org/tlog-cosignature)).
    #[cfg(feature = "ml_dsa")]
    MlDsa44SubtreeV1 = 0x06,
}

impl SignatureType {
    /// Returns the wire-format byte for this signature type.
    pub fn as_byte(self) -> u8 {
        self as u8
    }

    /// Parses a wire-format byte into a `SignatureType`.
    pub fn from_byte(b: u8) -> Result<Self, NoteError> {
        match b {
            0x01 => Ok(Self::Ed25519),
            0x04 => Ok(Self::Ed25519CosignatureV1),
            #[cfg(feature = "ml_dsa")]
            0x06 => Ok(Self::MlDsa44SubtreeV1),
            _ => Err(NoteError::MalformedVerifyingKey),
        }
    }

    /// Builds the signed message for this signature type.
    pub fn message(
        self,
        checkpoint_text: &str,
        timestamp: Instant,
        #[cfg(not(feature = "ml_dsa"))] _cosigner_name: &str,
        #[cfg(feature = "ml_dsa")] cosigner_name: &str,
    ) -> Result<Vec<u8>, NoteError> {
        match self {
            Self::Ed25519 => Ok(checkpoint_text.as_bytes().to_vec()),
            Self::Ed25519CosignatureV1 => {
                let epoch_secs = timestamp.into_unix_seconds() as u64;
                Ok(format!("cosignature/v1\ntime {}\n{}", epoch_secs, checkpoint_text).into_bytes())
            }
            #[cfg(feature = "ml_dsa")]
            Self::MlDsa44SubtreeV1 => {
                let checkpoint = crate::Checkpoint::parse(checkpoint_text)?;
                let epoch_secs = timestamp.into_unix_seconds() as u64;
                let mut msg = Vec::new();
                // label: "subtree/v1\n\0" (12 bytes)
                msg.extend_from_slice(b"subtree/v1\n\0");
                // cosigner_name: opaque<1..2^8-1>
                Self::push_opaque_u8(&mut msg, cosigner_name.as_bytes())?;
                // timestamp: 8-byte big-endian
                msg.extend_from_slice(&epoch_secs.to_be_bytes());
                // log_origin: opaque<1..2^8-1>
                Self::push_opaque_u8(&mut msg, checkpoint.origin.as_bytes())?;
                // start: 8-byte big-endian (0 for checkpoints)
                msg.extend_from_slice(&[0u8; 8]);
                // end: 8-byte big-endian (tree_size for checkpoints)
                msg.extend_from_slice(&checkpoint.tree_size.to_be_bytes());
                // hash: 32 bytes
                msg.extend_from_slice(checkpoint.root_hash.as_ref());
                Ok(msg)
            }
        }
    }

    /// Appends a TLS presentation language
    /// [`opaque<1..2^8-1>`](https://www.rfc-editor.org/rfc/rfc8446#section-3.4)
    /// field to `buf`: a 1-byte length prefix followed by the raw bytes.
    #[cfg(feature = "ml_dsa")]
    fn push_opaque_u8(buf: &mut Vec<u8>, data: &[u8]) -> Result<(), NoteError> {
        if data.len() > 255 {
            return Err(NoteError::OpaqueDataTooLong);
        }
        buf.push(data.len() as u8);
        buf.extend_from_slice(data);
        Ok(())
    }
}

/// The signing key material held by a [`NoteSigningKey`].
///
/// The enum variant determines both the key algorithm and the signing
/// behaviour.  This mirrors the [`VerifyingKey`] enum on the verification
/// side.
#[allow(clippy::large_enum_variant)]
pub enum SigningKey {
    /// Ed25519 log key — signs the checkpoint text directly (type 0x01).
    Ed25519(ed25519_dalek::SigningKey),
    /// Ed25519 cosignature key — signs the `cosignature/v1` message (type
    /// 0x04).
    Ed25519CosignatureV1(ed25519_dalek::SigningKey),
    /// ML-DSA-44 key — signs the `subtree/v1` message (type 0x06).
    /// Used by both log origins and witnesses.
    #[cfg(feature = "ml_dsa")]
    MlDsa44SubtreeV1(ml_dsa_44::KeyPair),
}

/// The verifying key material stored in a [`NoteVerifyingKey`].
///
/// The enum variant determines both the key algorithm and the C2SP
/// [signature type](https://c2sp.org/signed-note#signature-types).
#[derive(Debug, Clone, PartialEq)]
#[allow(clippy::large_enum_variant)]
pub enum VerifyingKey {
    /// Ed25519 log key (type 0x01) — verifies a direct Ed25519 signature
    /// over the checkpoint text.
    Ed25519(ed25519_dalek::VerifyingKey),
    /// Ed25519 cosignature key (type 0x04) — verifies a timestamped
    /// Ed25519 witness cosignature
    /// ([c2sp.org/tlog-cosignature](https://c2sp.org/tlog-cosignature)).
    Ed25519CosignatureV1(ed25519_dalek::VerifyingKey),
    /// ML-DSA-44 key (type 0x06) — verifies a timestamped ML-DSA-44
    /// (sub)tree signature. Used by both log origins and witnesses.
    ///
    /// See [FIPS 204](https://csrc.nist.gov/pubs/fips/204/final) and
    /// [c2sp.org/tlog-cosignature](https://c2sp.org/tlog-cosignature).
    #[cfg(feature = "ml_dsa")]
    MlDsa44SubtreeV1(ml_dsa_44::VerifyingKey),
}

impl Eq for VerifyingKey {}

impl VerifyingKey {
    /// Returns the [`SignatureType`] for this key.
    pub fn signature_type(&self) -> SignatureType {
        match self {
            Self::Ed25519(_) => SignatureType::Ed25519,
            Self::Ed25519CosignatureV1(_) => SignatureType::Ed25519CosignatureV1,
            #[cfg(feature = "ml_dsa")]
            Self::MlDsa44SubtreeV1(_) => SignatureType::MlDsa44SubtreeV1,
        }
    }
}

/// A signing key in note format, with metadata for deriving the
/// corresponding [`NoteVerifyingKey`].
pub struct NoteSigningKey {
    signing_key: SigningKey,
    origin: String,
    key_id_hint: [u8; 4],
}

impl NoteSigningKey {
    /// Creates a new `NoteSigningKey` from an origin string and a
    /// [`SigningKey`] variant.
    ///
    /// The key ID hint is computed automatically from the origin, the
    /// signature type implied by the variant, and the public key bytes.
    pub fn new(origin: &str, signing_key: SigningKey) -> Self {
        let key_id_hint = match &signing_key {
            SigningKey::Ed25519(signing_key) => compute_key_id(
                origin,
                SignatureType::Ed25519,
                &signing_key.verifying_key().to_bytes(),
            ),
            SigningKey::Ed25519CosignatureV1(signing_key) => compute_key_id(
                origin,
                SignatureType::Ed25519CosignatureV1,
                &signing_key.verifying_key().to_bytes(),
            ),
            #[cfg(feature = "ml_dsa")]
            SigningKey::MlDsa44SubtreeV1(key_pair) => compute_key_id(
                origin,
                SignatureType::MlDsa44SubtreeV1,
                key_pair.verifying_key().as_ref(),
            ),
        };
        Self { signing_key, origin: origin.to_string(), key_id_hint }
    }

    /// Derives the corresponding [`NoteVerifyingKey`] from this signing key.
    pub fn verifying_key(&self) -> NoteVerifyingKey {
        let vk = match &self.signing_key {
            SigningKey::Ed25519(signing_key) => VerifyingKey::Ed25519(signing_key.verifying_key()),
            SigningKey::Ed25519CosignatureV1(signing_key) => {
                VerifyingKey::Ed25519CosignatureV1(signing_key.verifying_key())
            }
            #[cfg(feature = "ml_dsa")]
            SigningKey::MlDsa44SubtreeV1(key_pair) => {
                VerifyingKey::MlDsa44SubtreeV1(key_pair.verifying_key().clone())
            }
        };
        NoteVerifyingKey {
            origin: self.origin.clone(),
            key_id_hint: self.key_id_hint,
            verifying_key: vk,
        }
    }

    /// Produces a [`NoteSignature`] over the given checkpoint, dispatching
    /// based on the key variant.
    pub fn sign(
        &self,
        checkpoint_text: &str,
        timestamp: Instant,
    ) -> Result<NoteSignature, NoteError> {
        let message = self.signature_type().message(checkpoint_text, timestamp, &self.origin)?;

        let sig_bytes = match &self.signing_key {
            SigningKey::Ed25519(sk) => {
                let signature = sk.sign(&message);
                signature.to_bytes().to_vec()
            }
            SigningKey::Ed25519CosignatureV1(sk) => {
                let signature = sk.sign(&message);
                TimestampedSignature { timestamp, signature: signature.to_bytes().to_vec() }
                    .to_bytes()
            }
            #[cfg(feature = "ml_dsa")]
            SigningKey::MlDsa44SubtreeV1(kp) => {
                let sig = kp.sign(&message).map_err(|_| NoteError::SignatureVerificationFailed)?;
                TimestampedSignature { timestamp, signature: sig.as_ref().to_vec() }.to_bytes()
            }
        };

        Ok(NoteSignature { origin: self.origin.clone(), key_id_hint: self.key_id_hint, sig_bytes })
    }

    /// Returns the [`SignatureType`] for this key.
    pub fn signature_type(&self) -> SignatureType {
        match &self.signing_key {
            SigningKey::Ed25519(_) => SignatureType::Ed25519,
            SigningKey::Ed25519CosignatureV1(_) => SignatureType::Ed25519CosignatureV1,
            #[cfg(feature = "ml_dsa")]
            SigningKey::MlDsa44SubtreeV1(_) => SignatureType::MlDsa44SubtreeV1,
        }
    }
}

/// A wrapper around a signature that includes a timestamp.
struct TimestampedSignature {
    timestamp: Instant,
    signature: Vec<u8>,
}

impl TimestampedSignature {
    /// Serialises the timestamped signature to bytes.
    ///
    /// The format is a big-endian 64-bit Unix timestamp followed by the
    /// raw signature bytes.
    fn to_bytes(&self) -> Vec<u8> {
        let epoch_secs = self.timestamp.into_unix_seconds() as u64;
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&epoch_secs.to_be_bytes());
        bytes.extend_from_slice(&self.signature);
        bytes
    }
}

/// A verifying key for a checkpoint signature in note format.
///
/// Supports Ed25519 log signatures (type 0x01), timestamped Ed25519 witness
/// cosignatures (type 0x04), and timestamped ML-DSA-44 signatures (type
/// 0x06) as defined by the
/// [C2SP signed-note specification](https://c2sp.org/signed-note) and the
/// [tlog-cosignature specification](https://c2sp.org/tlog-cosignature).
///
/// ML-DSA-44 (type 0x06) may be used by both log origins and witnesses.
#[derive(Debug, Clone, PartialEq)]
pub struct NoteVerifyingKey {
    pub origin: String,
    pub key_id_hint: [u8; 4],
    pub verifying_key: VerifyingKey,
}

impl Eq for NoteVerifyingKey {}

impl NoteVerifyingKey {
    /// Creates a new `NoteVerifyingKey` from an origin string and a
    /// [`VerifyingKey`] variant.
    ///
    /// The key ID hint is computed automatically from the origin, the
    /// signature type implied by the variant, and the public key bytes.
    pub fn new(origin: &str, verifying_key: VerifyingKey) -> Self {
        let key_id_hint = match &verifying_key {
            VerifyingKey::Ed25519(verifying_key) => {
                compute_key_id(origin, SignatureType::Ed25519, &verifying_key.to_bytes())
            }
            VerifyingKey::Ed25519CosignatureV1(verifying_key) => compute_key_id(
                origin,
                SignatureType::Ed25519CosignatureV1,
                &verifying_key.to_bytes(),
            ),
            #[cfg(feature = "ml_dsa")]
            VerifyingKey::MlDsa44SubtreeV1(verifying_key) => {
                compute_key_id(origin, SignatureType::MlDsa44SubtreeV1, verifying_key.as_ref())
            }
        };
        Self { verifying_key, origin: origin.to_string(), key_id_hint }
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
        if key_bytes.is_empty() {
            return Err(NoteError::MalformedVerifyingKey);
        }
        let key_id_hint: [u8; 4] =
            id_bytes.as_slice().try_into().map_err(|_| NoteError::MalformedVerifyingKey)?;

        let verifying_key = match SignatureType::from_byte(key_bytes[0])? {
            SignatureType::Ed25519 => {
                let raw: [u8; 32] =
                    key_bytes[1..].try_into().map_err(|_| NoteError::MalformedVerifyingKey)?;
                VerifyingKey::Ed25519(
                    ed25519_dalek::VerifyingKey::from_bytes(&raw)
                        .map_err(|_| NoteError::MalformedVerifyingKey)?,
                )
            }
            SignatureType::Ed25519CosignatureV1 => {
                let raw: [u8; 32] =
                    key_bytes[1..].try_into().map_err(|_| NoteError::MalformedVerifyingKey)?;
                VerifyingKey::Ed25519CosignatureV1(
                    ed25519_dalek::VerifyingKey::from_bytes(&raw)
                        .map_err(|_| NoteError::MalformedVerifyingKey)?,
                )
            }
            #[cfg(feature = "ml_dsa")]
            SignatureType::MlDsa44SubtreeV1 => {
                let vk = ml_dsa_44::VerifyingKey::try_from(&key_bytes[1..])
                    .map_err(|_| NoteError::MalformedVerifyingKey)?;
                VerifyingKey::MlDsa44SubtreeV1(vk)
            }
        };

        Ok(NoteVerifyingKey { origin, key_id_hint, verifying_key })
    }

    /// Serialises this verifying key back to note vkey string format:
    /// `<origin>+<hex key ID>+<base64(signature type || public key)>`.
    pub fn to_vkey_string(&self) -> String {
        let mut buf = alloc::vec![self.verifying_key.signature_type().as_byte()];
        match &self.verifying_key {
            VerifyingKey::Ed25519(vk) | VerifyingKey::Ed25519CosignatureV1(vk) => {
                buf.extend_from_slice(&vk.to_bytes());
            }
            #[cfg(feature = "ml_dsa")]
            VerifyingKey::MlDsa44SubtreeV1(vk) => buf.extend_from_slice(vk.as_ref()),
        }
        format!("{}+{}+{}", self.origin, hex::encode(self.key_id_hint), B64.encode(&buf))
    }

    /// Verifies that `sig` is a valid signature over the given checkpoint
    /// using this key, handling signature-type-specific payload framing.
    pub fn verify(&self, checkpoint_text: &str, sig: &NoteSignature) -> Result<(), NoteError> {
        match &self.verifying_key {
            VerifyingKey::Ed25519(vk) => {
                if sig.sig_bytes.len() != 64 {
                    return Err(NoteError::MalformedSignature);
                }
                let message =
                    SignatureType::Ed25519.message(checkpoint_text, Instant::UNIX_EPOCH, "")?;
                verify_ed25519(vk, &message, &sig.sig_bytes)
            }
            VerifyingKey::Ed25519CosignatureV1(vk) => {
                if sig.sig_bytes.len() <= 8 {
                    return Err(NoteError::MalformedSignature);
                }
                let timestamp_secs = u64::from_be_bytes(sig.sig_bytes[0..8].try_into().unwrap());
                let timestamp = Instant::from_unix_seconds(timestamp_secs as i64);
                let message = SignatureType::Ed25519CosignatureV1.message(
                    checkpoint_text,
                    timestamp,
                    &self.origin,
                )?;
                verify_ed25519(vk, &message, &sig.sig_bytes[8..])
            }
            #[cfg(feature = "ml_dsa")]
            VerifyingKey::MlDsa44SubtreeV1(vk) => {
                if sig.sig_bytes.len() <= 8 {
                    return Err(NoteError::MalformedSignature);
                }
                let timestamp_secs = u64::from_be_bytes(sig.sig_bytes[0..8].try_into().unwrap());
                let timestamp = Instant::from_unix_seconds(timestamp_secs as i64);
                let message = SignatureType::MlDsa44SubtreeV1.message(
                    checkpoint_text,
                    timestamp,
                    &self.origin,
                )?;
                verify_ml_dsa_44(vk, &message, &sig.sig_bytes[8..])
            }
        }
    }
}

/// Performs raw Ed25519 signature verification.
fn verify_ed25519(
    verifying_key: &ed25519_dalek::VerifyingKey,
    message: &[u8],
    signature: &[u8],
) -> Result<(), NoteError> {
    let sig =
        Signature::from_bytes(signature.try_into().map_err(|_| NoteError::MalformedSignature)?);
    verifying_key.verify(message, &sig).map_err(|_| NoteError::SignatureVerificationFailed)?;
    Ok(())
}

/// Performs ML-DSA-44 signature verification using
/// [FIPS 204](https://csrc.nist.gov/pubs/fips/204/final).
#[cfg(feature = "ml_dsa")]
fn verify_ml_dsa_44(
    verifying_key: &ml_dsa_44::VerifyingKey,
    message: &[u8],
    signature: &[u8],
) -> Result<(), NoteError> {
    let sig =
        ml_dsa_44::Signature::try_from(signature).map_err(|_| NoteError::MalformedSignature)?;
    if verifying_key.verify(message, &sig) {
        Ok(())
    } else {
        Err(NoteError::SignatureVerificationFailed)
    }
}

/// Computes the C2SP key ID hint:
/// `SHA-256(name || "\n" || type_byte || public_key_bytes)[:4]`.
fn compute_key_id(origin: &str, sig_type: SignatureType, key_bytes: &[u8]) -> [u8; 4] {
    let mut data = Vec::with_capacity(origin.len() + 2 + key_bytes.len());
    data.extend_from_slice(origin.as_bytes());
    data.push(b'\n');
    data.push(sig_type.as_byte());
    data.extend_from_slice(key_bytes);
    let hash: [u8; 32] = Sha256::from_contents(&data).into();
    hash[..4].try_into().unwrap()
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
        let b = B64.decode(encoded).map_err(|_| NoteError::MalformedSignature)?;
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
        assert!(matches!(
            NoteSignature::parse("— origin @@@@"),
            Err(NoteError::MalformedSignature)
        ));
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
    fn test_parse_verifying_key_ml_dsa_wrong_length() {
        // Type 0x06 but only 100 bytes of key material (need 1312).
        let mut key_bytes = alloc::vec![0x06u8];
        key_bytes.extend_from_slice(&[0u8; 100]);
        let key_b64 = B64.encode(&key_bytes);
        let serialized = format!("origin+12345678+{}", key_b64);
        assert!(matches!(
            NoteVerifyingKey::parse(&serialized),
            Err(NoteError::MalformedVerifyingKey)
        ));
    }

    #[test]
    fn test_verify_ed25519_wrong_key() {
        let signer = NoteSigningKey::new(
            "example.com/log",
            SigningKey::Ed25519(ed25519_dalek::SigningKey::from_bytes(&[42u8; 32])),
        );
        let other = NoteSigningKey::new(
            "example.com/log",
            SigningKey::Ed25519(ed25519_dalek::SigningKey::from_bytes(&[99u8; 32])),
        );
        let signed_text = "test message\n";
        let sig = signer.sign(signed_text, Instant::UNIX_EPOCH).unwrap();
        let result = other.verifying_key().verify(signed_text, &sig);
        assert!(matches!(result, Err(NoteError::SignatureVerificationFailed)));
    }

    #[test]
    fn test_roundtrip_vkey_string() {
        let key = NoteSigningKey::new(
            "example.com/log",
            SigningKey::Ed25519(ed25519_dalek::SigningKey::from_bytes(&[42u8; 32])),
        );
        let vkey_str = key.verifying_key().to_vkey_string();
        let parsed = NoteVerifyingKey::parse(&vkey_str).unwrap();
        assert_eq!(key.verifying_key(), parsed);
    }

    #[test]
    fn test_roundtrip_signature_line() {
        let key = NoteSigningKey::new(
            "example.com/log",
            SigningKey::Ed25519(ed25519_dalek::SigningKey::from_bytes(&[42u8; 32])),
        );
        let sig = key.sign("test payload\n", Instant::UNIX_EPOCH).unwrap();
        let line = sig.to_signature_line();
        let parsed = NoteSignature::parse(&line).unwrap();
        assert_eq!(sig.origin, parsed.origin);
        assert_eq!(sig.key_id_hint, parsed.key_id_hint);
        assert_eq!(sig.sig_bytes, parsed.sig_bytes);
    }

    #[test]
    fn test_cosignature_roundtrip() {
        let key = NoteSigningKey::new(
            "witness.example.com",
            SigningKey::Ed25519CosignatureV1(ed25519_dalek::SigningKey::from_bytes(&[43u8; 32])),
        );
        let checkpoint = "example.com/log\n42\nhash\n";
        let sig = key.sign(checkpoint, Instant::from_unix_seconds(1700000000)).unwrap();
        assert!(key.verifying_key().verify(checkpoint, &sig).is_ok());
    }

    #[test]
    fn test_matches_key() {
        let key = NoteSigningKey::new(
            "example.com/log",
            SigningKey::Ed25519(ed25519_dalek::SigningKey::from_bytes(&[42u8; 32])),
        );
        let sig = key.sign("test\n", Instant::UNIX_EPOCH).unwrap();
        assert!(sig.matches_key(&key.verifying_key()));

        let other = NoteSigningKey::new(
            "other.com/log",
            SigningKey::Ed25519(ed25519_dalek::SigningKey::from_bytes(&[99u8; 32])),
        );
        assert!(!sig.matches_key(&other.verifying_key()));
    }

    #[test]
    fn test_type_byte() {
        let log_key = NoteSigningKey::new(
            "example.com/log",
            SigningKey::Ed25519(ed25519_dalek::SigningKey::from_bytes(&[42u8; 32])),
        );
        assert_eq!(log_key.verifying_key().verifying_key.signature_type(), SignatureType::Ed25519);

        let cosigner = NoteSigningKey::new(
            "witness",
            SigningKey::Ed25519CosignatureV1(ed25519_dalek::SigningKey::from_bytes(&[43u8; 32])),
        );
        assert_eq!(
            cosigner.verifying_key().verifying_key.signature_type(),
            SignatureType::Ed25519CosignatureV1
        );

        let kp = ml_dsa_44::generate_key_pair().unwrap();
        let ml_key = NoteSigningKey::new("ml-witness", SigningKey::MlDsa44SubtreeV1(kp));
        assert_eq!(
            ml_key.verifying_key().verifying_key.signature_type(),
            SignatureType::MlDsa44SubtreeV1
        );
    }

    #[test]
    fn test_ml_dsa_vkey_roundtrip() {
        let kp = ml_dsa_44::generate_key_pair().unwrap();
        let vkey = NoteVerifyingKey::new(
            "ml-dsa-witness.example.com",
            VerifyingKey::MlDsa44SubtreeV1(kp.verifying_key().clone()),
        );
        assert_eq!(vkey.verifying_key.signature_type(), SignatureType::MlDsa44SubtreeV1);

        let vkey_str = vkey.to_vkey_string();
        let parsed = NoteVerifyingKey::parse(&vkey_str).unwrap();
        assert_eq!(vkey, parsed);
    }

    #[test]
    fn test_ml_dsa_cosignature_verify() {
        // Generate a real ML-DSA-44 keypair.
        let kp = ml_dsa_44::generate_key_pair().unwrap();

        let cosigner_name = "ml-dsa-witness.example.com";
        let log_origin = "example.com/log";
        let tree_size: u64 = 100;
        let root_hash = Sha256::from([0xCC_u8; 32]);
        let root_b64 = B64.encode(root_hash);
        let checkpoint_text = alloc::format!("{log_origin}\n{tree_size}\n{root_b64}\n");
        let timestamp = Instant::from_unix_seconds(1700000000_i64);

        // Build the cosigned_message via SignatureType.
        let message = SignatureType::MlDsa44SubtreeV1
            .message(&checkpoint_text, timestamp, cosigner_name)
            .unwrap();

        // Sign the message.
        let sig = kp.sign(&message).unwrap();

        // Build the timestamped signature (8-byte timestamp || sig).
        let mut ts_sig = Vec::new();
        ts_sig.extend_from_slice(&1700000000_u64.to_be_bytes());
        ts_sig.extend_from_slice(sig.as_ref());

        // Build the NoteVerifyingKey from the real public key.
        let vkey = NoteVerifyingKey::new(
            cosigner_name,
            VerifyingKey::MlDsa44SubtreeV1(kp.verifying_key().clone()),
        );

        // Build a NoteSignature.
        let note_sig = NoteSignature {
            origin: cosigner_name.to_string(),
            key_id_hint: vkey.key_id_hint,
            sig_bytes: ts_sig,
        };

        // Verify — should succeed.
        assert!(vkey.verify(&checkpoint_text, &note_sig).is_ok());
    }

    #[test]
    fn test_ml_dsa_cosignature_wrong_key() {
        let kp1 = ml_dsa_44::generate_key_pair().unwrap();
        let kp2 = ml_dsa_44::generate_key_pair().unwrap();

        let cosigner_name = "witness.example.com";
        let log_origin = "example.com/log";
        let tree_size: u64 = 50;
        let root_hash = Sha256::from([0xDD_u8; 32]);
        let root_b64 = B64.encode(root_hash);
        let checkpoint_text = alloc::format!("{log_origin}\n{tree_size}\n{root_b64}\n");
        let timestamp = Instant::from_unix_seconds(1700000001_i64);

        let message = SignatureType::MlDsa44SubtreeV1
            .message(&checkpoint_text, timestamp, cosigner_name)
            .unwrap();
        let sig = kp1.sign(&message).unwrap();

        let mut ts_sig = Vec::new();
        ts_sig.extend_from_slice(&1700000001_u64.to_be_bytes());
        ts_sig.extend_from_slice(sig.as_ref());

        // Build verifying key from kp2 (wrong key).
        let vkey = NoteVerifyingKey::new(
            cosigner_name,
            VerifyingKey::MlDsa44SubtreeV1(kp2.verifying_key().clone()),
        );
        let note_sig = NoteSignature {
            origin: cosigner_name.to_string(),
            key_id_hint: vkey.key_id_hint,
            sig_bytes: ts_sig,
        };

        let result = vkey.verify(&checkpoint_text, &note_sig);
        assert!(matches!(result, Err(NoteError::SignatureVerificationFailed)));
    }

    #[test]
    fn test_ml_dsa_cosignature_wrong_length() {
        let kp = ml_dsa_44::generate_key_pair().unwrap();
        let vkey = NoteVerifyingKey::new(
            "witness",
            VerifyingKey::MlDsa44SubtreeV1(kp.verifying_key().clone()),
        );

        // Signature with wrong length (too short).
        let note_sig = NoteSignature {
            origin: "witness".to_string(),
            key_id_hint: vkey.key_id_hint,
            sig_bytes: alloc::vec![0u8; 100],
        };

        let h = Sha256::from([0u8; 32]);
        let root_b64 = B64.encode(h);
        let checkpoint_text = alloc::format!("origin\n0\n{root_b64}\n");
        let result = vkey.verify(&checkpoint_text, &note_sig);
        assert!(matches!(result, Err(NoteError::MalformedSignature)));
    }

    #[test]
    fn test_ml_dsa_log_signing_roundtrip() {
        let kp = ml_dsa_44::generate_key_pair().unwrap();
        let log_origin = "example.com/log";
        let tree_size: u64 = 100;
        let root_hash = Sha256::from([0xCC_u8; 32]);
        let root_b64 = B64.encode(root_hash);
        let timestamp = Instant::from_unix_seconds(1700000000);
        let checkpoint = alloc::format!("{log_origin}\n{tree_size}\n{root_b64}\n");

        let log_key = NoteSigningKey::new(log_origin, SigningKey::MlDsa44SubtreeV1(kp));
        let sig = log_key.sign(&checkpoint, timestamp).unwrap();
        let vkey = log_key.verifying_key();
        assert!(vkey.verify(&checkpoint, &sig).is_ok());
    }
}
