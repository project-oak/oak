//
// Copyright 2023 The Project Oak Authors
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

use alloc::{string::String, vec::Vec};
use core::cmp::Ordering;

use anyhow::Context;
use ecdsa::signature::Verifier;
use oak_proto_rust::oak::{
    attestation::v1::{Event, KeyType, Signature, TimestampReferenceValue, VerifyingKeySet},
    HexDigest, RawDigest,
};
use oak_time::{Duration, Instant};
use p256::pkcs8::{der::Decode, DecodePublicKey};
use prost::Message;
use prost_types::Any;
use sha2::{Digest, Sha256, Sha384, Sha512};

const PUBLIC_KEY_PEM_LABEL: &str = "PUBLIC KEY";

/// Converts a raw ASN.1 DER public key bytes to PEM with a "PUBLIC KEY" label.
#[allow(unused)]
pub fn convert_raw_to_pem(asn1_der_public_key_bytes: &[u8]) -> String {
    let doc = p256::pkcs8::Document::from_der(asn1_der_public_key_bytes)
        .expect("public key bytes are not ASN.1 DER");
    doc.to_pem(PUBLIC_KEY_PEM_LABEL, p256::pkcs8::LineEnding::LF).expect("couldn't create pem")
}

/// Converts a PEM public key to raw ASN.1 DER bytes.
pub fn convert_pem_to_raw(public_key_pem: &str) -> anyhow::Result<Vec<u8>> {
    let (label, key) = p256::pkcs8::Document::from_pem(public_key_pem)
        .map_err(|e| anyhow::anyhow!("Couldn't interpret PEM: {e}"))?;

    anyhow::ensure!(
        label == PUBLIC_KEY_PEM_LABEL,
        "PEM label {label} is not {PUBLIC_KEY_PEM_LABEL}"
    );

    Ok(key.into_vec())
}

/// Converts ASN.1 DER public key bytes to a [`p256::ecdsa::VerifyingKey`].
pub fn convert_raw_to_verifying_key(
    public_key: &[u8],
) -> anyhow::Result<p256::ecdsa::VerifyingKey> {
    let doc = p256::pkcs8::Document::from_der(public_key)
        .map_err(|e| anyhow::anyhow!("Could not interpret bytes as ASN.1 DER: {e}"))?;
    p256::ecdsa::VerifyingKey::from_public_key_der(doc.as_bytes())
        .map_err(|e| anyhow::anyhow!("couldn't convert der to verifying key: {e}"))
}

/// Compares two ECDSA public keys.
///
/// Instead of comparing the bytes, we parse the
/// bytes and compare p256 keys. Keys are considered equal if they are the same
/// on the elliptic curve. This means that the keys could have different bytes,
/// but still be the same key.
pub fn equal_keys(public_key_a: &[u8], public_key_b: &[u8]) -> anyhow::Result<bool> {
    let key_a = convert_raw_to_verifying_key(public_key_a)?;
    let key_b = convert_raw_to_verifying_key(public_key_b)?;
    Ok(key_a.cmp(&key_b) == Ordering::Equal)
}

/// Verifies a signature against a key set, given the signed contents.
pub fn verify_signature(
    signature: &Signature,
    contents: &[u8],
    key_set: &VerifyingKeySet,
) -> anyhow::Result<()> {
    let key = key_set
        .keys
        .iter()
        .find(|k| k.key_id == signature.key_id)
        .ok_or_else(|| anyhow::anyhow!("could not find key id in key set"))?;
    match key.r#type() {
        KeyType::Undefined => anyhow::bail!("Undefined key type"),
        KeyType::EcdsaP256Sha256 => verify_signature_ecdsa(&signature.raw, contents, &key.raw),
    }
}

/// Verifies the signature over the contents using the public key.
pub fn verify_signature_ecdsa(
    signature: &[u8],
    contents: &[u8],
    public_key: &[u8],
) -> anyhow::Result<()> {
    let sig = ecdsa::Signature::from_der(signature)
        .map_err(|error| anyhow::anyhow!("invalid ASN.1 signature: {}", error))?;
    let key = convert_raw_to_verifying_key(public_key)
        .map_err(|error| anyhow::anyhow!("couldn't convert public key: {error}"))?;

    key.verify(contents, &sig)
        .map_err(|error| anyhow::anyhow!("couldn't verify signature: {}", error))
}

/// Verifies the given timestamp is valid based on the current time and the
/// TimestampReferenceValue.
pub fn verify_timestamp(
    current_time: Instant,
    timestamp: Instant,
    reference_value: &TimestampReferenceValue,
) -> anyhow::Result<()> {
    // if not_before_absolute is set, check that the timestamp is not before
    // that time.
    if let Some(not_before_absolute) = &reference_value.not_before_absolute {
        let not_before_absolute_time = Instant::from(not_before_absolute);
        if timestamp < not_before_absolute_time {
            anyhow::bail!(
                "Timestamp is too early: timestamp = {}, must not be before = {}",
                timestamp,
                not_before_absolute_time
            );
        }
    }

    // if not_before_relative is set, check that the given timestamp is not
    // after the current time plus that (signed) duration.
    if let Some(not_before_relative) = &reference_value.not_before_relative {
        let offset = Duration::from(not_before_relative);
        if timestamp < current_time + offset {
            anyhow::bail!(
                "Timestamp is out of range: timestamp = {}, range [{}, {}]",
                timestamp,
                current_time + offset,
                current_time
            );
        }
    }

    Ok(())
}

pub fn hash_sha2_256(input: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(input);
    hasher.finalize().into()
}

fn hash_sha2_512(input: &[u8]) -> [u8; 64] {
    let mut hasher = Sha512::new();
    hasher.update(input);
    hasher.finalize().into()
}

fn hash_sha2_384(input: &[u8]) -> [u8; 48] {
    let mut hasher = Sha384::new();
    hasher.update(input);
    hasher.finalize().into()
}

/// Computes various digest formats of a binary array.
/// The empty arrays need to be filled, when we depend on SHA{1,3} hashers.
pub fn raw_digest_from_contents(contents: &[u8]) -> RawDigest {
    RawDigest {
        sha2_256: hash_sha2_256(contents).to_vec(),
        sha2_512: hash_sha2_512(contents).to_vec(),
        sha2_384: hash_sha2_384(contents).to_vec(),
        ..Default::default()
    }
}

#[derive(PartialEq)]
pub enum MatchResult {
    Same = 0,
    Different = 1,
    Undecidable = 2,
    Contradictory = 3,
}

/// Compares two digests instances for equality.
///
/// All available fields in both inputs are taken into account for the decision.
/// If it is undesirable to include the weak sha1 hash in the decision simply
/// remove it from either input.
///
/// [`Same`] if underlying binaries are the same, [`Different`] if they differ.
/// [`Undecidable`] if the constellation in the protos doesn't provide enough
/// information, [`Contradictory`] if the constellation suggest same and
/// different at the same time. [`Undecidable`] and [`Contradictory`] usually
/// point to problems which are unlikely to be addressable at run time.
pub fn get_hex_digest_match(a: &HexDigest, b: &HexDigest) -> MatchResult {
    let mut same = 0;
    let mut different = 0;

    let mut compare = |a: &str, b: &str| {
        if !a.is_empty() && !b.is_empty() {
            if a == b {
                same += 1;
            } else {
                different += 1;
            }
        }
    };

    compare(&a.psha2, &b.psha2);
    compare(&a.sha1, &b.sha1);
    compare(&a.sha2_256, &b.sha2_256);
    compare(&a.sha2_512, &b.sha2_512);
    compare(&a.sha3_512, &b.sha3_512);
    compare(&a.sha3_384, &b.sha3_384);
    compare(&a.sha3_256, &b.sha3_256);
    compare(&a.sha3_224, &b.sha3_224);
    compare(&a.sha2_384, &b.sha2_384);

    #[allow(clippy::collapsible_else_if)]
    if same > 0 {
        if different > 0 {
            MatchResult::Contradictory
        } else {
            MatchResult::Same
        }
    } else {
        if different > 0 {
            MatchResult::Different
        } else {
            MatchResult::Undecidable
        }
    }
}

/// Compares two raw digests.
pub fn get_raw_digest_match(a: &RawDigest, b: &RawDigest) -> MatchResult {
    get_hex_digest_match(&raw_to_hex_digest(a), &raw_to_hex_digest(b))
}

pub fn is_hex_digest_match(actual: &HexDigest, expected: &HexDigest) -> anyhow::Result<()> {
    match get_hex_digest_match(actual, expected) {
        MatchResult::Same => Ok(()),
        MatchResult::Different => {
            Err(anyhow::anyhow!("mismatched digests: expected={expected:?} actual={actual:?}",))
        }
        MatchResult::Undecidable => Err(anyhow::anyhow!("invalid digests")),
        MatchResult::Contradictory => Err(anyhow::anyhow!("hash collision")),
    }
}

pub fn is_raw_digest_match(actual: &RawDigest, expected: &RawDigest) -> anyhow::Result<()> {
    match get_raw_digest_match(actual, expected) {
        MatchResult::Same => Ok(()),
        MatchResult::Different => {
            Err(anyhow::anyhow!("mismatched digests: expected={expected:?} actual={actual:?}",))
        }
        MatchResult::Undecidable => Err(anyhow::anyhow!("invalid digests")),
        MatchResult::Contradictory => Err(anyhow::anyhow!("hash collision")),
    }
}

/// Converts raw digest to hex digest.
pub fn raw_to_hex_digest(r: &RawDigest) -> HexDigest {
    HexDigest {
        psha2: hex::encode(&r.psha2),
        sha1: hex::encode(&r.sha1),
        sha2_256: hex::encode(&r.sha2_256),
        sha2_512: hex::encode(&r.sha2_512),
        sha3_512: hex::encode(&r.sha3_512),
        sha3_384: hex::encode(&r.sha3_384),
        sha3_256: hex::encode(&r.sha3_256),
        sha3_224: hex::encode(&r.sha3_224),
        sha2_384: hex::encode(&r.sha2_384),
    }
}

/// Converts hex digest to raw digest.
pub fn hex_to_raw_digest(h: &HexDigest) -> anyhow::Result<RawDigest> {
    let hex_decode = |field, name| {
        hex::decode(field).map_err(|error| {
            anyhow::anyhow!("could not decode field {name}: {error} (value {field})")
        })
    };

    let raw = RawDigest {
        psha2: hex_decode(&h.psha2, "psha2")?,
        sha1: hex_decode(&h.sha1, "sha1")?,
        sha2_256: hex_decode(&h.sha2_256, "sha2_256")?,
        sha2_512: hex_decode(&h.sha2_512, "sha2_512")?,
        sha3_512: hex_decode(&h.sha3_512, "sha3_512")?,
        sha3_384: hex_decode(&h.sha3_384, "sha3_384")?,
        sha3_256: hex_decode(&h.sha3_256, "sha3_256")?,
        sha3_224: hex_decode(&h.sha3_224, "sha3_224")?,
        sha2_384: hex_decode(&h.sha2_384, "sha2_384")?,
    };

    Ok(raw)
}

/// Decodes a serialized event into a specified [`Message`].
pub fn decode_event_proto<M: Message + Default>(
    expected_type_url: &str,
    encoded_event: &[u8],
) -> anyhow::Result<M> {
    let event_proto = Event::decode(encoded_event)
        .map_err(|error| anyhow::anyhow!("failed to decode event: {}", error))?;
    decode_protobuf_any::<M>(
        expected_type_url,
        event_proto.event.as_ref().context("no event found in the `event` field")?,
    )
}

/// Decodes [`Any`] message into a specified [`Message`].
pub fn decode_protobuf_any<M: Message + Default>(
    expected_type_url: &str,
    message: &Any,
) -> anyhow::Result<M> {
    if message.type_url.as_str() != expected_type_url {
        anyhow::bail!(
            "expected message with type url: {}, found: {}",
            expected_type_url,
            message.type_url.as_str()
        );
    }
    M::decode(message.value.as_ref()).map_err(|error| {
        anyhow::anyhow!(
            "couldn't decode `google.protobuf.Any` message into {}: {:?}",
            expected_type_url,
            error
        )
    })
}

#[cfg(test)]
mod tests;
