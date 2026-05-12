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

mod json;
mod pae;

#[cfg(test)]
mod tests;

use alloc::vec::Vec;

use anyhow::Context;
use oak_digest::Sha256;
use oak_proto_rust::{
    google::pes::v1::{
        PublicEndorsement, VerificationMaterial as ProtoVerificationMaterial,
        verification_material::VerificationMaterial,
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

/// Decodes a PES confirmation from JSON format.
fn parse_pes_confirmation(pes_confirmation_bytes: &[u8]) -> anyhow::Result<PublicEndorsement> {
    let json_val = json::PublicEndorsement::try_from(pes_confirmation_bytes)
        .context("failed to parse PES confirmation JSON")?;

    // Only attempt to parse as a PES JSON confirmation if it looks like an object
    // that belongs to us, avoiding false positives on random valid JSON
    // strings/numbers.
    if json_val.statement.is_none() && json_val.name.is_none() {
        anyhow::bail!("JSON does not look like a PES confirmation");
    }

    Ok(PublicEndorsement::from(json_val))
}
