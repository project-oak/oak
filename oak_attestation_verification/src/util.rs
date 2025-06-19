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

use alloc::{string::String, vec, vec::Vec};
use core::cmp::Ordering;

use anyhow::Context;
use ecdsa::signature::Verifier;
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, extracted_evidence::EvidenceValues, kernel_binary_reference_value,
        reference_values, root_layer_data::Report, text_reference_value, AmdSevReferenceValues,
        ApplicationLayerReferenceValues, BinaryReferenceValue, ContainerLayerReferenceValues,
        Digests, Event, ExtractedEvidence, InsecureReferenceValues, KernelBinaryReferenceValue,
        KernelDigests, KernelLayerData, KernelLayerReferenceValues, KeyType,
        OakContainersReferenceValues, OakRestrictedKernelReferenceValues, ReferenceValues,
        RootLayerData, RootLayerReferenceValues, Signature, SkipVerification, StringLiterals,
        SystemLayerReferenceValues, TextReferenceValue, TimestampReferenceValue, Validity,
        VerifyingKeySet,
    },
    HexDigest, RawDigest,
};
use p256::pkcs8::{der::Decode, DecodePublicKey};
use prost::Message;
use prost_types::Any;
use sha2::{Digest, Sha256, Sha384, Sha512};
use time::{Duration, OffsetDateTime};

use crate::statement;

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
    now_utc_millis: i64,
    timestamp: &OffsetDateTime,
    reference_value: &TimestampReferenceValue,
) -> anyhow::Result<()> {
    // if not_before_absolute is set, check that the timestamp is not before that
    // time.
    if let Some(not_before_absolute) = &reference_value.not_before_absolute {
        let not_before_absolute_time = OffsetDateTime::UNIX_EPOCH
            + Duration::new(not_before_absolute.seconds, not_before_absolute.nanos);
        if *timestamp < not_before_absolute_time {
            anyhow::bail!(
                "Timestamp is too early: timestamp = {:?}, must not be before = {:?}",
                *timestamp,
                not_before_absolute_time
            );
        }
    }

    // if not_before_relative is set, check that the given timestamp is after or
    // equal to the current time plus that (signed) duration.
    if let Some(not_before_relative) = &reference_value.not_before_relative {
        let offset = Duration::new(not_before_relative.seconds, not_before_relative.nanos);
        let current_time = OffsetDateTime::UNIX_EPOCH + Duration::milliseconds(now_utc_millis);
        if *timestamp < current_time + offset {
            anyhow::bail!(
                "Timestamp is out of range: timestamp = {:?}, range [{:?}, {:?}]",
                *timestamp,
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

pub fn reference_values_from_evidence(evidence: ExtractedEvidence) -> ReferenceValues {
    let r#type = match evidence.evidence_values.expect("no evidence") {
        EvidenceValues::OakRestrictedKernel(rk) => {
            let application = rk.application_layer.expect("no application layer evidence");
            let config = application.config.expect("no application config digest");
            Some(reference_values::Type::OakRestrictedKernel(OakRestrictedKernelReferenceValues {
                root_layer: Some(root_layer_reference_values_from_evidence(
                    rk.root_layer.expect("no root layer evidence"),
                )),
                kernel_layer: Some(kernel_layer_reference_values_from_evidence(
                    rk.kernel_layer.expect("no kernel layer evidence"),
                )),
                application_layer: Some(ApplicationLayerReferenceValues {
                    binary: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(Digests {
                            digests: vec![application
                                .binary
                                .expect("no application binary digest")],
                        })),
                    }),
                    // We don't currently specify configuration values for Oak Containers
                    // applications, so skip for now if the sha2_256 value is empty.
                    configuration: if config.sha2_256.is_empty() {
                        Some(BinaryReferenceValue {
                            r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
                        })
                    } else {
                        Some(BinaryReferenceValue {
                            r#type: Some(binary_reference_value::Type::Digests(Digests {
                                digests: vec![config],
                            })),
                        })
                    },
                }),
            }))
        }
        EvidenceValues::OakContainers(oc) => {
            let system = oc.system_layer.expect("no system layer evidence");
            let container = oc.container_layer.expect("no container layer evidence");
            Some(reference_values::Type::OakContainers(OakContainersReferenceValues {
                root_layer: Some(root_layer_reference_values_from_evidence(
                    oc.root_layer.expect("no root layer evidence"),
                )),
                kernel_layer: Some(kernel_layer_reference_values_from_evidence(
                    oc.kernel_layer.expect("no kernel layer evidence"),
                )),
                system_layer: Some(SystemLayerReferenceValues {
                    system_image: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(Digests {
                            digests: vec![system.system_image.expect("no system image digest")],
                        })),
                    }),
                }),
                container_layer: Some(ContainerLayerReferenceValues {
                    binary: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(Digests {
                            digests: vec![container.bundle.expect("no container bundle digest")],
                        })),
                    }),
                    configuration: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(Digests {
                            digests: vec![container.config.expect("no container config digest")],
                        })),
                    }),
                }),
            }))
        }
        EvidenceValues::Cb(_) => panic!("not yet supported"),
        EvidenceValues::Standalone(_) => panic!("not yet supported"),
    };
    ReferenceValues { r#type }
}

fn root_layer_reference_values_from_evidence(
    root_layer: RootLayerData,
) -> RootLayerReferenceValues {
    let amd_sev = root_layer.report.clone().and_then(|report| match report {
        Report::SevSnp(r) => Some(AmdSevReferenceValues {
            min_tcb_version: r.current_tcb,
            stage0: Some(BinaryReferenceValue {
                r#type: Some(binary_reference_value::Type::Digests(Digests {
                    digests: vec![RawDigest {
                        sha2_384: r.initial_measurement,
                        ..Default::default()
                    }],
                })),
            }),
            allow_debug: r.debug,
        }),
        _ => None,
    });
    let intel_tdx = if let Some(Report::Tdx(_)) = root_layer.report.clone() {
        panic!("not yet supported");
    } else {
        None
    };
    let insecure = root_layer.report.and_then(|report| match report {
        Report::Fake(_) => Some(InsecureReferenceValues {}),
        _ => None,
    });
    RootLayerReferenceValues { amd_sev, intel_tdx, insecure }
}

fn kernel_layer_reference_values_from_evidence(
    kernel_layer: KernelLayerData,
) -> KernelLayerReferenceValues {
    #[allow(deprecated)]
    KernelLayerReferenceValues {
        kernel: Some(KernelBinaryReferenceValue {
            r#type: Some(kernel_binary_reference_value::Type::Digests(KernelDigests {
                image: Some(Digests {
                    digests: vec![kernel_layer.kernel_image.expect("no kernel image digest")],
                }),
                setup_data: Some(Digests {
                    digests: vec![kernel_layer
                        .kernel_setup_data
                        .expect("no kernel setup data digest")],
                }),
            })),
        }),
        kernel_cmd_line_text: Some(TextReferenceValue {
            r#type: Some(text_reference_value::Type::StringLiterals(StringLiterals {
                value: vec![kernel_layer.kernel_raw_cmd_line.expect("no kernel command-line")],
            })),
        }),
        init_ram_fs: Some(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![kernel_layer.init_ram_fs.expect("no initial ram disk digest")],
            })),
        }),
        memory_map: Some(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![kernel_layer.memory_map.expect("no memory map digest")],
            })),
        }),
        acpi: Some(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![kernel_layer.acpi.expect("no acpi digest")],
            })),
        }),
    }
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

/// Return a milliseconds-since-the-epoch timestamp value.
///
/// Endorsement validity structures in our JSON-based endorsements use
/// milliseconds resolution, but [`OffsetDateTime`] provides only seconds or
/// nanoseconds since the epoch.
///
/// This bridges a convenience gap, and helps with readability of code that
/// works with validity times.
pub trait UnixTimestampMillis {
    fn unix_timestamp_millis(&self) -> i64;
}

impl UnixTimestampMillis for OffsetDateTime {
    fn unix_timestamp_millis(&self) -> i64 {
        self.unix_timestamp() * 1000
    }
}

impl From<&statement::Validity> for Validity {
    fn from(value: &statement::Validity) -> Validity {
        Validity {
            not_before: value.not_before.unix_timestamp_millis(),
            not_after: value.not_after.unix_timestamp_millis(),
        }
    }
}

#[cfg(test)]
mod tests;
