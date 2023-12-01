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

//! Provides verification based on evidence, endorsements and reference values.

use crate::alloc::string::ToString;

use crate::proto::oak::attestation::v1::{
    attestation_results::Status, endorsements, reference_values, AttestationResults,
    CbEndorsements, CbReferenceValues, Endorsements, Evidence, OakContainersEndorsements,
    OakContainersReferenceValues, OakRestrictedKernelEndorsements,
    OakRestrictedKernelReferenceValues, ReferenceValues,
};

use coset::{cwt::ClaimsSet, CborSerializable, CoseKey};
use ecdsa::{signature::Verifier, Signature};
use oak_dice::cert::{cose_key_to_verifying_key, get_public_key_from_claims_set};

// We don't use additional authenticated data.
const ADDITIONAL_DATA: &[u8] = b"";

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
    verify_dice_chain(evidence)?;

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

/// Verifies signatures along the certificate chain induced by DICE layers.
fn verify_dice_chain(evidence: &Evidence) -> anyhow::Result<()> {
    let root_layer = evidence
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer evidence"))?;
    let cose_key = CoseKey::from_slice(&root_layer.eca_public_key)
        .map_err(|_cose_err| anyhow::anyhow!("couldn't deserialize root layer public key"))?;
    let mut verifying_key =
        cose_key_to_verifying_key(&cose_key).map_err(|msg| anyhow::anyhow!(msg))?;

    for layer in evidence.layers.iter() {
        let cert = coset::CoseSign1::from_slice(&layer.eca_certificate)
            .map_err(|_cose_err| anyhow::anyhow!("could not parse certificate"))?;
        cert.verify_signature(ADDITIONAL_DATA, |signature, contents| {
            let sig = Signature::from_slice(signature)?;
            verifying_key.verify(contents, &sig)
        })?;
        let payload = cert
            .payload
            .ok_or_else(|| anyhow::anyhow!("no cert payload"))?;
        let claims = ClaimsSet::from_slice(&payload)
            .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))?;
        let cose_key =
            get_public_key_from_claims_set(&claims).map_err(|msg| anyhow::anyhow!(msg))?;
        verifying_key = cose_key_to_verifying_key(&cose_key).map_err(|msg| anyhow::anyhow!(msg))?;
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
    Ok(()) // TODO(#4074): Needs implementation, work in progress.
}

fn verify_cb(
    _evidence: &Evidence,
    _endorsements: &CbEndorsements,
    _reference_values: &CbReferenceValues,
) -> anyhow::Result<()> {
    anyhow::bail!("Needs implementation")
}
