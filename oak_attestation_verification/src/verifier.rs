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

//! Provides top-level verification based on evidence, endorsments and reference values.

use crate::alloc::string::ToString;

use crate::{
    proto::oak::attestation::v1::{
        attestation_results::Status, endorsements, reference_values, AttestationResults,
        CbEndorsements, CbReferenceValues, Endorsements, Evidence, OakContainersEndorsements,
        OakContainersReferenceValues, OakRestrictedKernelEndorsements,
        OakRestrictedKernelReferenceValues, ReferenceValues,
    },
    util::cose_key_to_verifying_key,
};
use coset::{
    cbor::value::Value, cwt::ClaimsSet, CborSerializable, CoseKey, RegisteredLabelWithPrivate,
};
use ecdsa::{signature::Verifier, Signature};

// We don't use additional authenticated data.
const ADDITIONAL_DATA: &[u8] = b"";

/// ID for the CWT private claim corresponding to the Subject of the CWT.
/// NB: Copied from oak_dice crate.
const SUBJECT_PUBLIC_KEY_ID: i64 = -4670552;

/// Verifies entire setup by forwarding to individual setup types.
pub fn verify(
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> AttestationResults {
    match verify_internal(evidence, endorsements, reference_values).err() {
        Some(err) => AttestationResults {
            status: Status::GenericFailure.into(),
            reason: err.to_string(),
        },
        None => AttestationResults {
            status: Status::Success.into(),
            reason: "".to_string(),
        },
    }
}

/// Same as verify(), but with Rust-internal return value.
pub fn verify_internal(
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> anyhow::Result<()> {
    verify_certificate_chain(evidence)?;

    match (
        endorsements.r#type.as_ref(),
        reference_values.r#type.as_ref(),
    ) {
        (
            Some(endorsements::Type::OakRestrictedKernel(ends)),
            Some(reference_values::Type::OakRestrictedKernel(rvs)),
        ) => verify_oak_restricted_kernel(evidence, ends, rvs),
        (
            Some(endorsements::Type::OakContainers(ends)),
            Some(reference_values::Type::OakContainers(rvs)),
        ) => verify_oak_containers(evidence, ends, rvs),
        (Some(endorsements::Type::Cb(ends)), Some(reference_values::Type::Cb(rvs))) => {
            verify_cb(evidence, ends, rvs)
        }
        (None, None) => anyhow::bail!("Endorsements and reference values both empty"),
        (None, Some(_)) => anyhow::bail!("Endorsements are empty"),
        (Some(_), None) => anyhow::bail!("Reference values are empty"),
        (Some(_), Some(_)) => anyhow::bail!("Mismatch between endorsements and reference values"),
    }
}

fn verify_certificate_chain(evidence: &Evidence) -> anyhow::Result<()> {
    let root_layer = evidence
        .root_layer
        .as_ref()
        .ok_or(anyhow::anyhow!("no root layer evidence"))?;
    let cose_key = CoseKey::from_slice(&root_layer.eca_public_key)
        .map_err(|_cose_err| anyhow::anyhow!("couldn't deserialize root layer public key"))?;
    let mut verifying_key = cose_key_to_verifying_key(&cose_key)?;

    for layer in evidence.layers.iter() {
        let cert = coset::CoseSign1::from_slice(&layer.eca_certificate)
            .map_err(|_cose_err| anyhow::anyhow!("could not parse certificate"))?;
        cert.verify_signature(ADDITIONAL_DATA, |signature, contents| {
            let sig = Signature::from_slice(signature)?;
            verifying_key.verify(contents, &sig)
        })?;
        let payload = cert.payload.ok_or(anyhow::anyhow!("no cert payload"))?;
        let claims = ClaimsSet::from_slice(&payload)
            .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))?;
        let cose_key = get_public_key_from_claims_set(&claims)?;
        verifying_key = cose_key_to_verifying_key(&cose_key)?;
    }

    Ok(())
}

fn verify_oak_restricted_kernel(
    _evidence: &Evidence,
    _endorsements: &OakRestrictedKernelEndorsements,
    _reference_values: &OakRestrictedKernelReferenceValues,
) -> anyhow::Result<()> {
    anyhow::bail!("Needs implementation")
}

fn verify_oak_containers(
    _evidence: &Evidence,
    _endorsements: &OakContainersEndorsements,
    _reference_values: &OakContainersReferenceValues,
) -> anyhow::Result<()> {
    Ok(()) // Work in progress
}

fn verify_cb(
    _evidence: &Evidence,
    _endorsements: &CbEndorsements,
    _reference_values: &CbReferenceValues,
) -> anyhow::Result<()> {
    anyhow::bail!("Needs implementation")
}

/// Extracts the certified public key from the claims set of a certificate.
/// NB: Copied from oak_dice crate.
fn get_public_key_from_claims_set(claims: &ClaimsSet) -> anyhow::Result<CoseKey> {
    let public_key_bytes = claims
        .rest
        .iter()
        .find_map(|(label, value)| {
            if let Value::Bytes(bytes) = value
                && label == &RegisteredLabelWithPrivate::PrivateUse(SUBJECT_PUBLIC_KEY_ID)
            {
                Some(bytes)
            } else {
                None
            }
        })
        .ok_or(anyhow::anyhow!("public key not found in claims"))?;
    CoseKey::from_slice(public_key_bytes)
        .map_err(|_cose_err| anyhow::anyhow!("couldn't deserialize public key"))
}
