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

use crate::{
    claims::{get_digest, parse_endorsement_statement},
    endorsement::verify_binary_endorsement,
    proto::oak::attestation::v1::{
        attestation_results::Status, binary_reference_value, endorsements, reference_values,
        AttestationResults, BinaryReferenceValue, CbEndorsements, CbReferenceValues, Endorsements,
        Evidence, KernelLayerEndorsements, KernelLayerReferenceValues, OakContainersEndorsements,
        OakContainersReferenceValues, OakRestrictedKernelEndorsements,
        OakRestrictedKernelReferenceValues, ReferenceValues, RootLayerEndorsements,
        RootLayerReferenceValues, StringReferenceValue, TransparentReleaseEndorsement,
    },
    util::{hex_to_raw_digest, is_raw_digest_match, MatchResult},
};

use coset::{cwt::ClaimsSet, CborSerializable, CoseKey};
use ecdsa::{signature::Verifier, Signature};
use oak_dice::cert::{cose_key_to_verifying_key, get_public_key_from_claims_set};

// We don't use additional authenticated data.
const ADDITIONAL_DATA: &[u8] = b"";

/// Verifies entire setup by forwarding to individual setup types.
/// The `now_utc_millis` argument will be changed to a time type as work progresses.
pub fn verify(
    now_utc_millis: i64,
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> AttestationResults {
    match verify_internal(now_utc_millis, evidence, endorsements, reference_values).err() {
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
    now_utc_millis: i64,
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
        ) => verify_oak_restricted_kernel(now_utc_millis, ends, rvs),
        (
            Some(endorsements::Type::OakContainers(ends)),
            Some(reference_values::Type::OakContainers(rvs)),
        ) => verify_oak_containers(now_utc_millis, ends, rvs),
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
    now_utc_millis: i64,
    endorsements: &OakRestrictedKernelEndorsements,
    reference_values: &OakRestrictedKernelReferenceValues,
) -> anyhow::Result<()> {
    // Bind references to layers to variables, for both endorsements and
    // reference values. The presence of all fields is necessary for
    // verification success - there are no exceptions.
    let e0 = endorsements
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer endorsements"))?;
    let e1 = endorsements
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel layer endorsements"))?;
    let e2 = endorsements
        .application_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no application layer endorsements"))?;

    let r0 = reference_values
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;
    let r1 = reference_values
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;
    let r2 = reference_values
        .application_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;

    // Verify Transparent Release endorsements in root layer.
    verify_root_layer_endorsements(now_utc_millis, e0, r0)?;

    // Verify Transparent Release endorsements in kernel layer.
    verify_kernel_layer_endorsements(now_utc_millis, e1, r1)?;

    // Verify Transparent Release endorsements in application layer.
    let e20 = e2
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary endorsement"))?;

    let r20 = r2
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e20, r20)?;

    let e21 = e2
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no configuration endorsement"))?;

    let r21 = r2
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no configuration reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e21, r21)
}

fn verify_oak_containers(
    now_utc_millis: i64,
    endorsements: &OakContainersEndorsements,
    reference_values: &OakContainersReferenceValues,
) -> anyhow::Result<()> {
    // Bind references to layers to variables.
    let e0 = endorsements
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer endorsements"))?;
    let e1 = endorsements
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel layer endorsements"))?;
    let e2 = endorsements
        .system_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system layer endorsements"))?;
    let e3 = endorsements
        .container_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no container layer endorsements"))?;

    let r0 = reference_values
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;
    let r1 = reference_values
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;
    let r2 = reference_values
        .system_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;
    let r3 = reference_values
        .container_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;

    // Verify Transparent Release endorsements in root layer.
    verify_root_layer_endorsements(now_utc_millis, e0, r0)?;

    // Verify Transparent Release endorsements in kernel layer.
    verify_kernel_layer_endorsements(now_utc_millis, e1, r1)?;

    // Verify Transparent Release endorsements in system layer.
    let e20 = e2
        .system_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system image endorsement"))?;

    let r20 = r2
        .system_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system image reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e20, r20)?;

    let e21 = e2
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no configuration endorsement"))?;

    let r21 = r2
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no configuration reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e21, r21)?;

    // Verify Transparent Release endorsements in container layer.
    let e30 = e3
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary endorsement"))?;

    let r30 = r3
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e30, r30)?;

    let e31 = e3
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary endorsement"))?;

    let r31 = r3
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e31, r31)
}

fn verify_cb(
    _evidence: &Evidence,
    _endorsements: &CbEndorsements,
    _reference_values: &CbReferenceValues,
) -> anyhow::Result<()> {
    anyhow::bail!("Needs implementation")
}

fn verify_transparent_release_endorsement(
    now_utc_millis: i64,
    endorsement: &TransparentReleaseEndorsement,
    reference_value: &BinaryReferenceValue,
) -> anyhow::Result<()> {
    let statement = parse_endorsement_statement(&endorsement.endorsement)?;
    let hex_digest = get_digest(&statement)?;
    let expected = hex_to_raw_digest(&hex_digest)?;

    match reference_value.r#type.as_ref() {
        Some(binary_reference_value::Type::Endorsement(erv)) => verify_binary_endorsement(
            now_utc_millis,
            &endorsement.endorsement,
            &endorsement.rekor_log_entry,
            &erv.endorser_public_key,
            &erv.rekor_public_key,
        ),
        Some(binary_reference_value::Type::Digests(ds)) => {
            if ds
                .digests
                .iter()
                .any(|actual| is_raw_digest_match(actual, &expected) == MatchResult::SAME)
            {
                Ok(())
            } else {
                anyhow::bail!("digests do not match");
            }
        }
        None => anyhow::bail!("empty binary reference value"),
    }
}

/// Verifies all ingredients of the kernel layer, which is common to both
/// Oak Restricted Kernel and Oak Containers setups.
fn verify_root_layer_endorsements(
    now_utc_millis: i64,
    e0: &RootLayerEndorsements,
    r0: &RootLayerReferenceValues,
) -> anyhow::Result<()> {
    let e00 = e0
        .stage0
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no stage0 endorsement"))?;

    let r00 = r0
        .amd_sev
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no amd_sev in root reference values"))?
        .stage0
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no stage0 reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e00, r00)
}

/// Verifies all ingredients of the kernel layer, which is common to both
/// Oak Restricted Kernel and Oak Containers setups.
fn verify_kernel_layer_endorsements(
    now_utc_millis: i64,
    e1: &KernelLayerEndorsements,
    r1: &KernelLayerReferenceValues,
) -> anyhow::Result<()> {
    let e10 = e1
        .kernel_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel endorsement"))?;

    let r10 = r1
        .kernel_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e10, r10)?;

    let e11 = e1
        .kernel_cmd_line
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data endorsement"))?;

    let r11 = r1
        .kernel_cmd_line
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data reference value"))?;

    verify_string_value_endorsement(now_utc_millis, e11, r11)?;

    let e12 = e1
        .kernel_setup_data
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data endorsement"))?;

    let r12 = r1
        .kernel_setup_data
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e12, r12)?;

    let e13 = e1
        .init_ram_fs
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel init ram fs endorsement"))?;

    let r13 = r1
        .init_ram_fs
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel init ram fs reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e13, r13)?;

    Ok(())
}

fn verify_string_value_endorsement(
    _now_utc_millis: i64,
    _end: &TransparentReleaseEndorsement,
    _rv: &StringReferenceValue,
) -> anyhow::Result<()> {
    Ok(()) // Needs implementation
}
