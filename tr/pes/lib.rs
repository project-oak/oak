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

use anyhow::Context;
use oak_digest::Sha256;
use oak_proto_rust::{google::pes::v1::PublicEndorsement, oak::attestation::v1::VerifyingKeySet};
use prost::Message;

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
    let public_endorsement = PublicEndorsement::decode(pes_confirmation_bytes)
        .map_err(|e| anyhow::anyhow!("failed to decode PublicEndorsement: {}", e))?;

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

    let endorser_public_key_der = match endorser_vm.verification_material.as_ref().ok_or_else(|| anyhow::anyhow!("missing verification_material oneof"))? {
        oak_proto_rust::google::pes::v1::verification_material::VerificationMaterial::X509Certificate(cert) => {
            &cert.der_bytes
        }
        oak_proto_rust::google::pes::v1::verification_material::VerificationMaterial::EcdsaP256Sha256(pubkey) => {
            &pubkey.der_bytes
        }
    };

    // Construct the Pre-Authentication Encoding (PAE) canonical byte string.
    let pae_bytes = pae::calculate(
        &endorsement.serialized,
        endorser_public_key_der,
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

    let pes_public_key_der = match pes_vm.verification_material.as_ref().ok_or_else(|| anyhow::anyhow!("missing PES verification_material oneof"))? {
        oak_proto_rust::google::pes::v1::verification_material::VerificationMaterial::X509Certificate(cert) => {
            &cert.der_bytes
        }
        oak_proto_rust::google::pes::v1::verification_material::VerificationMaterial::EcdsaP256Sha256(pubkey) => {
            &pubkey.der_bytes
        }
    };

    // Find the PES key in the trusted set (Reference Value)
    let trusted_key = pes_key_set
        .keys
        .iter()
        .find(|k| k.raw == *pes_public_key_der)
        .ok_or_else(|| anyhow::anyhow!("PES public key not found in trusted key set"))?;

    match trusted_key.r#type() {
        oak_proto_rust::oak::attestation::v1::KeyType::Undefined => {
            anyhow::bail!("Undefined key type")
        }
        oak_proto_rust::oak::attestation::v1::KeyType::EcdsaP256Sha256 => {
            key_util::verify_signature_ecdsa(
                &pes_signature.signature,
                &pae_bytes,
                pes_public_key_der,
            )
            .context("failed to verify ECDSA signature")?;
        }
        oak_proto_rust::oak::attestation::v1::KeyType::RsaSha2256 => {
            key_util::verify_signature_rsa(
                &pes_signature.signature,
                &pae_bytes,
                pes_public_key_der,
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
