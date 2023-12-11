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
        ApplicationLayerEndorsements, ApplicationLayerReferenceValues, AttestationResults,
        BinaryReferenceValue, CbEndorsements, CbReferenceValues, ContainerLayerEndorsements,
        ContainerLayerReferenceValues, Endorsements, Evidence, KernelLayerEndorsements,
        KernelLayerReferenceValues, OakContainersEndorsements, OakContainersReferenceValues,
        OakRestrictedKernelEndorsements, OakRestrictedKernelReferenceValues, ReferenceValues,
        RootLayerEndorsements, RootLayerReferenceValues, StringReferenceValue,
        SystemLayerEndorsements, SystemLayerReferenceValues, TransparentReleaseEndorsement,
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
    let e_root = endorsements
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer endorsements"))?;
    let r_root = reference_values
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;

    verify_root_layer_endorsements(now_utc_millis, e_root, r_root)?;

    let e_kernel = endorsements
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel layer endorsements"))?;
    let r_kernel = reference_values
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel layer reference values"))?;

    verify_kernel_layer_endorsements(now_utc_millis, e_kernel, r_kernel)?;

    let e_appl = endorsements
        .application_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no application layer endorsements"))?;
    let r_appl = reference_values
        .application_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no application layer reference values"))?;

    verify_application_layer_endorsements(now_utc_millis, e_appl, r_appl)
}

fn verify_oak_containers(
    now_utc_millis: i64,
    endorsements: &OakContainersEndorsements,
    reference_values: &OakContainersReferenceValues,
) -> anyhow::Result<()> {
    let e_root = endorsements
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer endorsements"))?;
    let r_root = reference_values
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;

    verify_root_layer_endorsements(now_utc_millis, e_root, r_root)?;

    let e_kernel = endorsements
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel layer endorsements"))?;
    let r_kernel = reference_values
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel layer reference values"))?;

    verify_kernel_layer_endorsements(now_utc_millis, e_kernel, r_kernel)?;

    let e_system = endorsements
        .system_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system layer endorsements"))?;
    let r_system = reference_values
        .system_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system layer reference values"))?;

    verify_system_layer_endorsements(now_utc_millis, e_system, r_system)?;

    let e_container = endorsements
        .container_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no container layer endorsements"))?;
    let r_container = reference_values
        .container_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no container layer reference values"))?;

    verify_container_layer_endorsements(now_utc_millis, e_container, r_container)
}

fn verify_cb(
    _evidence: &Evidence,
    _endorsements: &CbEndorsements,
    _reference_values: &CbReferenceValues,
) -> anyhow::Result<()> {
    anyhow::bail!("Needs implementation")
}

/// Verifies all ingredients of the kernel layer, which is common to both
/// Oak Restricted Kernel and Oak Containers setups.
fn verify_root_layer_endorsements(
    now_utc_millis: i64,
    e: &RootLayerEndorsements,
    r: &RootLayerReferenceValues,
) -> anyhow::Result<()> {
    let e_stage0 = e
        .stage0
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no stage0 endorsement"))?;

    let r_stage0 = r
        .amd_sev
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no amd_sev in root reference values"))?
        .stage0
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no stage0 reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e_stage0, r_stage0)
}

/// Verifies all ingredients of the kernel layer, which is common to both
/// Oak Restricted Kernel and Oak Containers setups.
fn verify_kernel_layer_endorsements(
    now_utc_millis: i64,
    e: &KernelLayerEndorsements,
    r: &KernelLayerReferenceValues,
) -> anyhow::Result<()> {
    let e_kernel_image = e
        .kernel_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel endorsement"))?;

    let r_kernel_image = r
        .kernel_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e_kernel_image, r_kernel_image)?;

    let e_kernel_cmd_line = e
        .kernel_cmd_line
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data endorsement"))?;

    let r_kernel_cmd_line = r
        .kernel_cmd_line
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data reference value"))?;

    verify_string_value_endorsement(now_utc_millis, e_kernel_cmd_line, r_kernel_cmd_line)?;

    let e_kernel_setup_data = e
        .kernel_setup_data
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data endorsement"))?;

    let r_kernel_setup_data = r
        .kernel_setup_data
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data reference value"))?;

    verify_transparent_release_endorsement(
        now_utc_millis,
        e_kernel_setup_data,
        r_kernel_setup_data,
    )?;

    let e_init_ram_fs = e
        .init_ram_fs
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel init ram fs endorsement"))?;

    let r_init_ram_fs = r
        .init_ram_fs
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel init ram fs reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e_init_ram_fs, r_init_ram_fs)
}

/// Verifies all ingredients of the system image layer for Oak Containers.
fn verify_system_layer_endorsements(
    now_utc_millis: i64,
    e: &SystemLayerEndorsements,
    r: &SystemLayerReferenceValues,
) -> anyhow::Result<()> {
    let e_system_image = e
        .system_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system image endorsement"))?;

    let r_system_image = r
        .system_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system image reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e_system_image, r_system_image)?;

    let e_config = e
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no configuration endorsement"))?;

    let r_config = r
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no configuration reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e_config, r_config)
}

/// Verifies all ingredients of the application layer for Oak Restricted Kernel.
fn verify_application_layer_endorsements(
    now_utc_millis: i64,
    e: &ApplicationLayerEndorsements,
    r: &ApplicationLayerReferenceValues,
) -> anyhow::Result<()> {
    // Verify Transparent Release endorsements in application layer.
    let e_binary = e
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary endorsement"))?;

    let r_binary = r
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e_binary, r_binary)?;

    let e_config = e
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no configuration endorsement"))?;

    let r_config = r
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no configuration reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e_config, r_config)
}

/// Verifies all ingredients of the container layer for Oak Containers.
fn verify_container_layer_endorsements(
    now_utc_millis: i64,
    e: &ContainerLayerEndorsements,
    r: &ContainerLayerReferenceValues,
) -> anyhow::Result<()> {
    let e30 = e
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary endorsement"))?;

    let r30 = r
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e30, r30)?;

    let e31 = e
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary endorsement"))?;

    let r31 = r
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary reference value"))?;

    verify_transparent_release_endorsement(now_utc_millis, e31, r31)
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

fn verify_string_value_endorsement(
    _now_utc_millis: i64,
    _end: &TransparentReleaseEndorsement,
    _rv: &StringReferenceValue,
) -> anyhow::Result<()> {
    Ok(()) // Needs implementation
}
