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

#![no_std]

extern crate alloc;

mod pae;

#[cfg(test)]
mod tests;

use alloc::{string::ToString, vec::Vec};

use anyhow::Context;
use oak_digest::Sha256;
use oak_proto_rust::{
    google::pes::v1::{
        EcdsaP256PublicKey, PublicEndorsement, Signature, Statement, TLogReceipt,
        VerificationMaterial as ProtoVerificationMaterial, X509Der,
        statement::Format as StatementFormat, verification_material::VerificationMaterial,
    },
    oak::attestation::v1::{KeyType, VerifyingKeySet},
};
use x509_cert::der::{Decode, Encode};

/// Verifies a PES confirmation (serialized PublicEndorsement) against a PES
/// public key set.
///
/// # Arguments
///
/// * `pes_confirmation_bytes`: The serialized `PublicEndorsement` proto from
///   PES.
/// * `pes_key_set`: The trusted public keys for verifying the PES signature.
/// * `expected_endorsement_bytes`: The expected serialized endorsement that
///   should match the one in the confirmation.
///
/// # Returns
///
/// `Ok(())` if verification succeeds, or an error otherwise.
pub fn verify_pes_confirmation(
    pes_confirmation_bytes: &[u8],
    pes_key_set: &VerifyingKeySet,
    expected_endorsement_bytes: &[u8],
) -> anyhow::Result<()> {
    let public_endorsement = parse_pes_confirmation(pes_confirmation_bytes)?;

    let endorsement = public_endorsement
        .statement
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("missing endorsement in PublicEndorsement"))?;

    let endorser_signature = public_endorsement
        .statement_signature
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("missing endorser_signature in PublicEndorsement"))?;

    let tlog_receipt = public_endorsement
        .tlog_receipt
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("missing tlog_receipt in PublicEndorsement"))?;

    // Extract raw DER bytes from endorser's verification material for PAE.
    // Note: The Java service signs the raw bytes (DER) of the certificate/key, not
    // the proto.
    let endorser_vm = endorser_signature
        .verification_material
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("missing verification_material"))?;

    let endorser_raw_vm_bytes = extract_raw_vm_bytes(endorser_vm)?;

    // Construct the Pre-Authentication Encoding (PAE) canonical byte string.
    let pae_bytes = pae::calculate(
        &endorsement.serialized,
        endorser_raw_vm_bytes,
        &endorser_signature.signature,
        &tlog_receipt.entry_id,
    );

    // Verify PES signature(s) using the trusted PES public key set.
    // The confirmation contains signatures from PES, so we must use PES's own keys
    // for verification.
    let pes_signature = public_endorsement
        .endorsement_signatures
        .first()
        .ok_or_else(|| anyhow::anyhow!("no endorsement signatures found"))?;

    // Extract PES public key from the PES signature's verification material
    let pes_vm = pes_signature
        .verification_material
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("missing PES verification_material"))?;

    let pes_public_key_der = extract_public_key_der(pes_vm)?;

    // Find the PES key in the trusted set (Reference Value)
    let trusted_key =
        pes_key_set.keys.iter().find(|k| k.raw == pes_public_key_der).ok_or_else(|| {
            let trusted_lengths: Vec<usize> =
                pes_key_set.keys.iter().map(|k| k.raw.len()).collect();
            anyhow::anyhow!(
                "PES public key not found in trusted key set.\n\
                 Expected key (from signature): {} bytes (hex: {})\n\
                 Trusted keys lengths: {:?}",
                pes_public_key_der.len(),
                hex::encode(&pes_public_key_der),
                trusted_lengths
            )
        })?;

    match trusted_key.r#type() {
        KeyType::Undefined => anyhow::bail!("Undefined key type"),
        KeyType::EcdsaP256Sha256 => {
            key_util::verify_signature_ecdsa(
                &pes_signature.signature,
                &pae_bytes,
                &pes_public_key_der,
            )
            .context("failed to verify ECDSA signature")?;
        }
        KeyType::RsaSha2256 => {
            key_util::verify_signature_rsa(
                &pes_signature.signature,
                &pae_bytes,
                &pes_public_key_der,
            )
            .context("failed to verify RSA signature")?;
        }
    }

    let actual_digest = Sha256::from_contents(&endorsement.serialized);
    let expected_digest = Sha256::from_contents(expected_endorsement_bytes);

    anyhow::ensure!(
        actual_digest == expected_digest,
        "endorsement digest mismatch: expected {}, actual {}",
        expected_digest.to_hex(),
        actual_digest.to_hex()
    );

    Ok(())
}

fn extract_raw_vm_bytes(vm: &ProtoVerificationMaterial) -> anyhow::Result<&[u8]> {
    let vm_oneof = vm
        .verification_material
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("missing verification_material oneof"))?;

    match vm_oneof {
        VerificationMaterial::X509Certificate(cert) => Ok(&cert.der_bytes),
        VerificationMaterial::EcdsaP256Sha256(pubkey) => Ok(&pubkey.der_bytes),
    }
}

fn extract_public_key_der(vm: &ProtoVerificationMaterial) -> anyhow::Result<Vec<u8>> {
    let vm_oneof = vm
        .verification_material
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("missing verification_material oneof"))?;

    match vm_oneof {
        VerificationMaterial::X509Certificate(cert) => {
            let parsed_cert = x509_cert::Certificate::from_der(&cert.der_bytes)
                .map_err(|e| anyhow::anyhow!("failed to parse PES X.509 cert: {e}"))?;
            let spki_der = parsed_cert
                .tbs_certificate
                .subject_public_key_info
                .to_der()
                .map_err(|e| anyhow::anyhow!("failed to serialize SPKI: {e}"))?;
            Ok(spki_der)
        }
        VerificationMaterial::EcdsaP256Sha256(pubkey) => Ok(pubkey.der_bytes.to_vec()),
    }
}

/// Helper to decode a base64 string from a JSON value.
fn parse_base64(val: Option<&serde_json::Value>) -> anyhow::Result<Vec<u8>> {
    let s = val
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow::anyhow!("expected string for base64 decoding"))?;
    use base64::{Engine as _, engine::general_purpose::STANDARD};
    STANDARD.decode(s).map_err(|e| anyhow::anyhow!("invalid base64: {}", e))
}

/// Helper to parse the nested VerificationMaterial
fn parse_verification_material(
    val: Option<&serde_json::Value>,
) -> anyhow::Result<Option<ProtoVerificationMaterial>> {
    let val = match val {
        Some(v) => v,
        None => return Ok(None),
    };

    if let Some(x509_val) = val.get("x509Certificate") {
        return Ok(Some(ProtoVerificationMaterial {
            verification_material: Some(VerificationMaterial::X509Certificate(X509Der {
                der_bytes: parse_base64(x509_val.get("derBytes"))?,
            })),
        }));
    }

    if let Some(ecdsa_val) = val.get("ecdsaP256Sha256") {
        return Ok(Some(ProtoVerificationMaterial {
            verification_material: Some(VerificationMaterial::EcdsaP256Sha256(
                EcdsaP256PublicKey { der_bytes: parse_base64(ecdsa_val.get("derBytes"))? },
            )),
        }));
    }

    Ok(None)
}

/// Helper to parse a Signature
fn parse_signature(val: &serde_json::Value) -> anyhow::Result<Signature> {
    Ok(Signature {
        signature: parse_base64(val.get("signature"))?,
        verification_material: parse_verification_material(val.get("verificationMaterial"))?,
    })
}

/// Decodes a PES confirmation from JSON format.
fn parse_pes_confirmation(pes_confirmation_bytes: &[u8]) -> anyhow::Result<PublicEndorsement> {
    let json_val: serde_json::Value = serde_json::from_slice(pes_confirmation_bytes)
        .context("failed to parse PES confirmation as JSON")?;

    // Only attempt to parse as a PES JSON confirmation if it looks like an object
    // that belongs to us, avoiding false positives on random valid JSON
    // strings/numbers.
    if !json_val.is_object()
        || (json_val.get("statement").is_none() && json_val.get("name").is_none())
    {
        anyhow::bail!("JSON does not look like a PES confirmation");
    }

    let name = json_val.get("name").and_then(|v| v.as_str()).unwrap_or("").to_string();

    let statement = json_val
        .get("statement")
        .map(|stmt_val| -> anyhow::Result<Statement> {
            let serialized = parse_base64(stmt_val.get("serialized"))?;

            let format = match stmt_val.get("format").and_then(|v| v.as_str()) {
                Some("JSON_INTOTO") => StatementFormat::JsonIntoto.into(),
                _ => StatementFormat::Unspecified.into(),
            };

            Ok(Statement { format, serialized })
        })
        .transpose()?;

    let statement_signature =
        json_val.get("statementSignature").map(parse_signature).transpose()?;

    let endorsement_signatures = json_val
        .get("endorsementSignatures")
        .map(|v| {
            v.as_array()
                .context("endorsementSignatures must be an array")?
                .iter()
                .map(parse_signature)
                .collect::<anyhow::Result<Vec<_>>>()
        })
        .transpose()?
        .unwrap_or_default();

    let tlog_receipt = json_val.get("tlogReceipt").map(|val| TLogReceipt {
        entry_id: val.get("entryId").and_then(|v| v.as_str()).unwrap_or("").to_string(),
    });

    Ok(PublicEndorsement {
        name,
        statement,
        statement_signature,
        endorsement_signatures,
        tlog_receipt,
    })
}
