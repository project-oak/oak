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

use alloc::vec::Vec;

use coset::{cbor::Value, cwt::ClaimsSet, CborSerializable, CoseKey, RegisteredLabelWithPrivate};
use ecdsa::{signature::Verifier, Signature};
use oak_dice::cert::{
    cose_key_to_hpke_public_key, cose_key_to_verifying_key, get_public_key_from_claims_set,
    ACPI_MEASUREMENT_ID, CONTAINER_IMAGE_ID, ENCLAVE_APPLICATION_LAYER_ID, INITRD_MEASUREMENT_ID,
    KERNEL_COMMANDLINE_MEASUREMENT_ID, KERNEL_LAYER_ID, KERNEL_MEASUREMENT_ID,
    LAYER_2_CODE_MEASUREMENT_ID, LAYER_3_CODE_MEASUREMENT_ID, LAYER_3_CONFIG_MEASUREMENT_ID,
    MEMORY_MAP_MEASUREMENT_ID, SETUP_DATA_MEASUREMENT_ID, SHA2_256_ID, SYSTEM_IMAGE_LAYER_ID,
};
use oak_sev_guest::guest::{AttestationReport, PolicyFlags};
use zerocopy::FromBytes;

use crate::{
    alloc::string::ToString,
    claims::{get_digest, parse_endorsement_statement},
    endorsement::verify_binary_endorsement,
    proto::oak::{
        attestation::v1::{
            attestation_results::Status, binary_reference_value, endorsements, reference_values,
            AmdSevReferenceValues, ApplicationKeys, ApplicationLayerEndorsements,
            ApplicationLayerReferenceValues, AttestationResults, BinaryReferenceValue,
            CbEndorsements, CbReferenceValues, ContainerLayerEndorsements,
            ContainerLayerReferenceValues, Endorsements, Evidence, IntelTdxReferenceValues,
            KernelLayerEndorsements, KernelLayerReferenceValues, LayerEvidence,
            OakContainersEndorsements, OakContainersReferenceValues,
            OakRestrictedKernelEndorsements, OakRestrictedKernelReferenceValues, ReferenceValues,
            RootLayerEndorsements, RootLayerEvidence, RootLayerReferenceValues,
            SystemLayerEndorsements, SystemLayerReferenceValues, TeePlatform,
            TransparentReleaseEndorsement,
        },
        RawDigest,
    },
    util::{
        hex_to_raw_digest, is_hex_digest_match, is_raw_digest_match, raw_to_hex_digest, MatchResult,
    },
};

// We don't use additional authenticated data.
const ADDITIONAL_DATA: &[u8] = b"";

pub struct DiceChainResult {
    encryption_public_key: Vec<u8>,
    signing_public_key: Vec<u8>,
}

impl From<&anyhow::Result<DiceChainResult>> for AttestationResults {
    fn from(value: &anyhow::Result<DiceChainResult>) -> Self {
        match value {
            Ok(dice_chain_result) => AttestationResults {
                status: Status::Success.into(),
                encryption_public_key: dice_chain_result.encryption_public_key.clone(),
                signing_public_key: dice_chain_result.signing_public_key.clone(),
                ..Default::default()
            },
            Err(err) => AttestationResults {
                status: Status::GenericFailure.into(),
                reason: err.to_string(),
                ..Default::default()
            },
        }
    }
}

/// Verifies entire setup by forwarding to individual setup types.
/// The `now_utc_millis` argument will be changed to a time type as work progresses.
pub fn verify(
    now_utc_millis: i64,
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> anyhow::Result<DiceChainResult> {
    let dice_chain_result = verify_dice_chain(evidence)?;

    // Evidence, endorsements and reference values must reflect the same chain
    // type. We start with matching endorsements against reference values
    // since their chain type is obvious. Mismatches with evidence will be
    // caught downstream.
    match (
        endorsements.r#type.as_ref(),
        reference_values.r#type.as_ref(),
    ) {
        (
            Some(endorsements::Type::OakRestrictedKernel(ends)),
            Some(reference_values::Type::OakRestrictedKernel(rvs)),
        ) => verify_oak_restricted_kernel(now_utc_millis, evidence, ends, rvs),
        (
            Some(endorsements::Type::OakContainers(ends)),
            Some(reference_values::Type::OakContainers(rvs)),
        ) => verify_oak_containers(now_utc_millis, evidence, ends, rvs),
        (Some(endorsements::Type::Cb(ends)), Some(reference_values::Type::Cb(rvs))) => {
            verify_cb(evidence, ends, rvs)
        }
        (None, None) => anyhow::bail!("Endorsements and reference values both empty"),
        (None, Some(_)) => anyhow::bail!("Endorsements are empty"),
        (Some(_), None) => anyhow::bail!("Reference values are empty"),
        (Some(_), Some(_)) => anyhow::bail!("Mismatch between endorsements and reference values"),
    }?;

    Ok(dice_chain_result)
}

/// Verifies signatures along the certificate chain induced by DICE layers.
fn verify_dice_chain(evidence: &Evidence) -> anyhow::Result<DiceChainResult> {
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

    // Verify application keys in evidence and extract public keys. The verifying key comes from the
    // last DICE layer.
    let appl_keys = evidence
        .application_keys
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no application fields in evidence"))?;

    // Process encryption certificate.
    let encryption_cert =
        coset::CoseSign1::from_slice(&appl_keys.encryption_public_key_certificate)
            .map_err(|_cose_err| anyhow::anyhow!("could not parse encryption certificate"))?;
    encryption_cert.verify_signature(ADDITIONAL_DATA, |signature, contents| {
        let sig = Signature::from_slice(signature)?;
        verifying_key.verify(contents, &sig)
    })?;
    let encryption_payload = encryption_cert
        .payload
        .ok_or_else(|| anyhow::anyhow!("no encryption cert payload"))?;
    let encryption_claims = ClaimsSet::from_slice(&encryption_payload)
        .map_err(|_cose_err| anyhow::anyhow!("could not parse encryption claims set"))?;
    let encryption_cose_key =
        get_public_key_from_claims_set(&encryption_claims).map_err(|msg| anyhow::anyhow!(msg))?;
    let encryption_public_key =
        cose_key_to_hpke_public_key(&encryption_cose_key).map_err(|msg| anyhow::anyhow!(msg))?;

    // Process signing certificate.
    let signing_cert = coset::CoseSign1::from_slice(&appl_keys.signing_public_key_certificate)
        .map_err(|_cose_err| anyhow::anyhow!("could not parse encryption certificate"))?;
    signing_cert.verify_signature(ADDITIONAL_DATA, |signature, contents| {
        let sig = Signature::from_slice(signature)?;
        verifying_key.verify(contents, &sig)
    })?;
    let signing_payload = signing_cert
        .payload
        .ok_or_else(|| anyhow::anyhow!("no signing cert payload"))?;
    let signing_claims = ClaimsSet::from_slice(&signing_payload)
        .map_err(|_cose_err| anyhow::anyhow!("could not parse signing claims set"))?;
    let signing_cose_key: CoseKey =
        get_public_key_from_claims_set(&signing_claims).map_err(|msg| anyhow::anyhow!(msg))?;
    let signing_verifying_key =
        cose_key_to_verifying_key(&signing_cose_key).map_err(|msg| anyhow::anyhow!(msg))?;
    let signing_public_key = signing_verifying_key.to_sec1_bytes().to_vec();

    Ok(DiceChainResult {
        encryption_public_key,
        signing_public_key,
    })
}

fn verify_oak_restricted_kernel(
    now_utc_millis: i64,
    evidence: &Evidence,
    endorsements: &OakRestrictedKernelEndorsements,
    reference_values: &OakRestrictedKernelReferenceValues,
) -> anyhow::Result<()> {
    let l_root = evidence
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer evidence"))?;
    let e_root = endorsements
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer endorsements"))?;
    let r_root = reference_values
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;

    verify_root_layer(now_utc_millis, l_root, e_root, r_root)?;

    if evidence.layers.len() != 1 {
        anyhow::bail!("wrong number of evidence layers");
    }

    let e_kernel = endorsements
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel layer endorsements"))?;
    let r_kernel = reference_values
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel layer reference values"))?;

    verify_kernel_layer(now_utc_millis, &evidence.layers[0], e_kernel, r_kernel)?;

    let l_appl = evidence
        .application_keys
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no application keys"))?;
    let e_appl = endorsements
        .application_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no application layer endorsements"))?;
    let r_appl = reference_values
        .application_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no application layer reference values"))?;

    verify_application_layer(now_utc_millis, l_appl, e_appl, r_appl)
}

fn verify_oak_containers(
    now_utc_millis: i64,
    evidence: &Evidence,
    endorsements: &OakContainersEndorsements,
    reference_values: &OakContainersReferenceValues,
) -> anyhow::Result<()> {
    let l_root = evidence
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer evidence"))?;
    let e_root = endorsements
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer endorsements"))?;
    let r_root = reference_values
        .root_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no root layer reference values"))?;

    verify_root_layer(now_utc_millis, l_root, e_root, r_root)?;

    if evidence.layers.len() != 2 {
        anyhow::bail!("wrong number of evidence layers");
    }

    let e_kernel = endorsements
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel layer endorsements"))?;
    let r_kernel = reference_values
        .kernel_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel layer reference values"))?;

    verify_kernel_layer(now_utc_millis, &evidence.layers[0], e_kernel, r_kernel)?;

    let e_system = endorsements
        .system_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system layer endorsements"))?;
    let r_system = reference_values
        .system_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system layer reference values"))?;

    verify_system_layer(now_utc_millis, &evidence.layers[1], e_system, r_system)?;

    let l_container = evidence
        .application_keys
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no application keys"))?;
    let e_container = endorsements
        .container_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no container layer endorsements"))?;
    let r_container = reference_values
        .container_layer
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no container layer reference values"))?;

    verify_container_layer(now_utc_millis, l_container, e_container, r_container)
}

fn verify_cb(
    _evidence: &Evidence,
    _endorsements: &CbEndorsements,
    _reference_values: &CbReferenceValues,
) -> anyhow::Result<()> {
    anyhow::bail!("needs implementation")
}

/// Verifies the AMD SEV attestation report.
fn verify_amd_sev_attestation_report(
    report: &[u8],
    reference_values: &AmdSevReferenceValues,
) -> anyhow::Result<()> {
    let parsed = AttestationReport::ref_from(report)
        .ok_or_else(|| anyhow::anyhow!("could not parse AMD SEV attestation report"))?;
    parsed.validate().map_err(|msg| anyhow::anyhow!(msg))?;
    let data = &parsed.data;

    // Verify that we are not in debug mode.
    if !reference_values.allow_debug {
        let policy_flags = data
            .policy
            .get_flags()
            .ok_or_else(|| anyhow::anyhow!("failed to parse flags"))?;
        if policy_flags.bits() & PolicyFlags::DEBUG.bits() != 0 {
            anyhow::bail!("debug mode not allowed");
        }
    }

    Ok(())
}

/// Verifies the Intel TDX attestation report.
fn verify_intel_tdx_attestation_report(
    _report: &[u8],
    _reference_values: &IntelTdxReferenceValues,
) -> anyhow::Result<()> {
    anyhow::bail!("needs implementation")
}

/// Verifies all ingredients of the root layer, which is common to both
/// Oak Restricted Kernel and Oak Containers setups.
fn verify_root_layer(
    now_utc_millis: i64,
    l: &RootLayerEvidence,
    e: &RootLayerEndorsements,
    r: &RootLayerReferenceValues,
) -> anyhow::Result<()> {
    match l.platform() {
        TeePlatform::Unspecified => anyhow::bail!("unspecified TEE platform"),
        TeePlatform::AmdSevSnp => {
            let amd_sev = r
                .amd_sev
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("no AMD SEV reference values"))?;
            verify_amd_sev_attestation_report(&l.remote_attestation_report, amd_sev)?
        }
        TeePlatform::IntelTdx => {
            let intel_tdx = r
                .intel_tdx
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("no Intel TDX reference values"))?;
            verify_intel_tdx_attestation_report(&l.remote_attestation_report, intel_tdx)?
        }
    }

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

    // WIP: Parse attestation report and verify stage0 measurement.
    verify_transparent_release_endorsement(now_utc_millis, e_stage0, r_stage0)
}

/// Verifies all ingredients of the kernel layer, which is common to both
/// Oak Restricted Kernel and Oak Containers setups.
fn verify_kernel_layer(
    now_utc_millis: i64,
    l: &LayerEvidence,
    e: &KernelLayerEndorsements,
    r: &KernelLayerReferenceValues,
) -> anyhow::Result<()> {
    let claims = claims_set_from_serialized_cert(&l.eca_certificate)?;

    let e_kernel_image = e
        .kernel_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel endorsement"))?;
    let r_kernel_image = r
        .kernel_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel reference value"))?;

    verify_item(
        &claims,
        KERNEL_LAYER_ID,
        KERNEL_MEASUREMENT_ID,
        now_utc_millis,
        e_kernel_image,
        r_kernel_image,
    )?;

    let e_kernel_cmd_line = e
        .kernel_cmd_line
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data endorsement"))?;
    let r_kernel_cmd_line = r
        .kernel_cmd_line
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data reference value"))?;

    verify_item(
        &claims,
        KERNEL_LAYER_ID,
        KERNEL_COMMANDLINE_MEASUREMENT_ID,
        now_utc_millis,
        e_kernel_cmd_line,
        r_kernel_cmd_line,
    )?;

    let e_kernel_setup_data = e
        .kernel_setup_data
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data endorsement"))?;
    let r_kernel_setup_data = r
        .kernel_setup_data
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no kernel setup data reference value"))?;

    verify_item(
        &claims,
        KERNEL_LAYER_ID,
        SETUP_DATA_MEASUREMENT_ID,
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

    verify_item(
        &claims,
        KERNEL_LAYER_ID,
        INITRD_MEASUREMENT_ID,
        now_utc_millis,
        e_init_ram_fs,
        r_init_ram_fs,
    )?;

    let e_memory_map = e
        .memory_map
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no memory map endorsement"))?;
    let r_memory_map = r
        .memory_map
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no memory map reference value"))?;

    verify_item(
        &claims,
        KERNEL_LAYER_ID,
        MEMORY_MAP_MEASUREMENT_ID,
        now_utc_millis,
        e_memory_map,
        r_memory_map,
    )?;

    let e_acpi = e
        .acpi
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no acpi endorsement"))?;
    let r_acpi = r
        .acpi
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no acpi reference value"))?;

    verify_item(
        &claims,
        KERNEL_LAYER_ID,
        ACPI_MEASUREMENT_ID,
        now_utc_millis,
        e_acpi,
        r_acpi,
    )
}

/// Verifies all ingredients of the system image layer for Oak Containers.
fn verify_system_layer(
    now_utc_millis: i64,
    l: &LayerEvidence,
    e: &SystemLayerEndorsements,
    r: &SystemLayerReferenceValues,
) -> anyhow::Result<()> {
    let claims = claims_set_from_serialized_cert(&l.eca_certificate)?;

    let e_system_image = e
        .system_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system image endorsement"))?;
    let r_system_image = r
        .system_image
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no system image reference value"))?;

    verify_item(
        &claims,
        SYSTEM_IMAGE_LAYER_ID,
        LAYER_2_CODE_MEASUREMENT_ID,
        now_utc_millis,
        e_system_image,
        r_system_image,
    )
}

/// Verifies all ingredients of the application layer for Oak Restricted Kernel.
fn verify_application_layer(
    now_utc_millis: i64,
    l: &ApplicationKeys,
    e: &ApplicationLayerEndorsements,
    r: &ApplicationLayerReferenceValues,
) -> anyhow::Result<()> {
    // WIP: Which of the two app certificates contains the claims?
    let claims = claims_set_from_serialized_cert(&l.signing_public_key_certificate)?;

    let e_binary = e
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary endorsement"))?;
    let r_binary = r
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary reference value"))?;

    verify_item(
        &claims,
        ENCLAVE_APPLICATION_LAYER_ID,
        LAYER_3_CODE_MEASUREMENT_ID, // This is confusing, use Layer 2 or Layer 3?
        now_utc_millis,
        e_binary,
        r_binary,
    )?;

    let e_config = e
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no configuration endorsement"))?;
    let r_config = r
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no configuration reference value"))?;

    verify_item(
        &claims,
        ENCLAVE_APPLICATION_LAYER_ID,
        LAYER_3_CONFIG_MEASUREMENT_ID, // This is confusing, use Layer 2 or Layer 3?
        // We shouldn't use the layer number in the constant names.
        now_utc_millis,
        e_config,
        r_config,
    )
}

/// Verifies all ingredients of the container layer for Oak Containers.
fn verify_container_layer(
    now_utc_millis: i64,
    l: &ApplicationKeys,
    e: &ContainerLayerEndorsements,
    r: &ContainerLayerReferenceValues,
) -> anyhow::Result<()> {
    // WIP: Which of the two app certificates contains the claims?
    let claims = claims_set_from_serialized_cert(&l.signing_public_key_certificate)?;

    let e_binary = e
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary endorsement"))?;
    let r_binary = r
        .binary
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary reference value"))?;

    verify_item(
        &claims,
        CONTAINER_IMAGE_ID, // Should this be CONTAINER_LAYER_ID?
        LAYER_3_CODE_MEASUREMENT_ID,
        now_utc_millis,
        e_binary,
        r_binary,
    )?;

    let e_config = e
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary endorsement"))?;
    let r_config = r
        .configuration
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no binary reference value"))?;

    verify_item(
        &claims,
        CONTAINER_IMAGE_ID, // Should this be CONTAINER_LAYER_ID?
        LAYER_3_CONFIG_MEASUREMENT_ID,
        now_utc_millis,
        e_config,
        r_config,
    )
}

/// Shorthand for verify_measurement + verify_transparent_release_endorsement.
fn verify_item(
    claims: &ClaimsSet,
    layer_id: i64,
    measurement_id: i64,
    now_utc_millis: i64,
    endorsement: &TransparentReleaseEndorsement,
    reference_value: &BinaryReferenceValue,
) -> anyhow::Result<()> {
    match reference_value.r#type.as_ref() {
        Some(binary_reference_value::Type::Skip(_)) => Ok(()),
        Some(_) => {
            verify_measurement(&endorsement.endorsement, claims, layer_id, measurement_id)?;
            verify_transparent_release_endorsement(now_utc_millis, endorsement, reference_value)
        }
        None => anyhow::bail!("empty binary reference value"),
    }
}

fn verify_measurement(
    endorsement_statment: &[u8],
    claims: &ClaimsSet,
    layer_id: i64,
    measurement_id: i64,
) -> anyhow::Result<()> {
    let raw = digest_from_claims_set(claims, layer_id, measurement_id)?;
    let expected = raw_to_hex_digest(&raw);
    let statement = parse_endorsement_statement(endorsement_statment)?;
    let actual = get_digest(&statement)?;
    match is_hex_digest_match(&actual, &expected) {
        MatchResult::SAME => Ok(()),
        MatchResult::DIFFERENT => anyhow::bail!(
            "bad digest for layer={} measurement={} expected={} actual={}",
            layer_id,
            measurement_id,
            expected.sha2_256,
            actual.sha2_256
        ),
        MatchResult::UNDECIDABLE => panic!("poorly populated digests"),
    }
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
        Some(binary_reference_value::Type::Skip(_)) => Ok(()),
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

/// Parses the CBOR map from a serizalized certificate.
fn claims_set_from_serialized_cert(slice: &[u8]) -> anyhow::Result<ClaimsSet> {
    let cert = coset::CoseSign1::from_slice(slice)
        .map_err(|_cose_err| anyhow::anyhow!("could not parse certificate"))?;
    let payload = cert
        .payload
        .ok_or_else(|| anyhow::anyhow!("no signing cert payload"))?;
    ClaimsSet::from_slice(&payload)
        .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))
}

/// Extracts a digest from the given labels from the claims set of a
/// certificate.
fn digest_from_claims_set(
    claims: &ClaimsSet,
    layer_id: i64,
    measurement_id: i64,
) -> anyhow::Result<RawDigest> {
    let hash_bytes = claims
        .rest
        .iter()
        .find_map(|(label, value)| {
            if let Value::Map(cbor_entries) = value
                && label == &RegisteredLabelWithPrivate::PrivateUse(layer_id)
            {
                for cbor_entry in cbor_entries {
                    if Value::Integer(measurement_id.into()) == cbor_entry.0 {
                        if let Value::Map(entries) = &cbor_entry.1 {
                            for entry in entries {
                                if Value::Integer(SHA2_256_ID.into()) == entry.0
                                    && let Value::Bytes(hash) = &entry.1
                                {
                                    return Some(hash);
                                }
                            }
                        }
                    }
                }
                None
            } else {
                None
            }
        })
        .ok_or(anyhow::anyhow!(
            "could not find layer={}, measurement={}, or no hash",
            layer_id,
            measurement_id
        ))?;
    Ok(RawDigest {
        sha2_256: hash_bytes.to_vec(),
        ..Default::default()
    })
}
