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

use anyhow::Context;
use coset::{cbor::Value, cwt::ClaimsSet, CborSerializable, CoseKey, RegisteredLabelWithPrivate};
use ecdsa::{signature::Verifier, Signature};
use oak_dice::cert::{
    cose_key_to_hpke_public_key, cose_key_to_verifying_key, get_public_key_from_claims_set,
    ACPI_MEASUREMENT_ID, CONTAINER_IMAGE_LAYER_ID, ENCLAVE_APPLICATION_LAYER_ID,
    FINAL_LAYER_CONFIG_MEASUREMENT_ID, INITRD_MEASUREMENT_ID, KERNEL_COMMANDLINE_MEASUREMENT_ID,
    KERNEL_LAYER_ID, KERNEL_MEASUREMENT_ID, LAYER_2_CODE_MEASUREMENT_ID,
    LAYER_3_CODE_MEASUREMENT_ID, MEMORY_MAP_MEASUREMENT_ID, SETUP_DATA_MEASUREMENT_ID, SHA2_256_ID,
    SYSTEM_IMAGE_LAYER_ID,
};
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results::Status, binary_reference_value, endorsements,
        extracted_evidence::EvidenceValues, reference_values, root_layer_data::Report,
        AmdAttestationReport, AmdSevReferenceValues, ApplicationKeys, ApplicationLayerData,
        ApplicationLayerEndorsements, ApplicationLayerReferenceValues, AttestationResults,
        BinaryReferenceValue, CbData, CbEndorsements, CbReferenceValues, ContainerLayerData,
        ContainerLayerEndorsements, ContainerLayerReferenceValues, Endorsements, Evidence,
        ExtractedEvidence, FakeAttestationReport, InsecureReferenceValues,
        IntelTdxAttestationReport, IntelTdxReferenceValues, KernelLayerData,
        KernelLayerEndorsements, KernelLayerReferenceValues, OakContainersData,
        OakContainersEndorsements, OakContainersReferenceValues, OakRestrictedKernelData,
        OakRestrictedKernelEndorsements, OakRestrictedKernelReferenceValues, ReferenceValues,
        RootLayerData, RootLayerEndorsements, RootLayerEvidence, RootLayerReferenceValues,
        SystemLayerData, SystemLayerEndorsements, SystemLayerReferenceValues, TcbVersion,
        TeePlatform, TransparentReleaseEndorsement,
    },
    HexDigest, RawDigest,
};
use oak_sev_snp_attestation_report::AttestationReport;
use x509_cert::{
    der::{Decode, DecodePem},
    Certificate,
};
use zerocopy::FromBytes;

use crate::{
    alloc::string::ToString,
    amd::{verify_attestation_report_signature, verify_cert_signature},
    claims::{get_digest, parse_endorsement_statement},
    endorsement::verify_binary_endorsement,
    util::{hash_sha2_256, is_hex_digest_match, raw_to_hex_digest, MatchResult},
};

const ASK_MILAN_CERT_PEM: &str = include_str!("../data/ask_milan.pem");

// We don't use additional authenticated data.
const ADDITIONAL_DATA: &[u8] = b"";

pub fn to_attestation_results(
    verify_result: &anyhow::Result<ExtractedEvidence>,
) -> AttestationResults {
    match verify_result {
        Ok(extracted_evidence) => AttestationResults {
            status: Status::Success.into(),
            encryption_public_key: extracted_evidence.encryption_public_key.clone(),
            signing_public_key: extracted_evidence.signing_public_key.clone(),
            ..Default::default()
        },
        Err(err) => AttestationResults {
            status: Status::GenericFailure.into(),
            reason: err.to_string(),
            ..Default::default()
        },
    }
}

/// Verifies entire setup by forwarding to individual setup types.
/// The `now_utc_millis` argument will be changed to a time type as work progresses.
pub fn verify(
    now_utc_millis: i64,
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> anyhow::Result<ExtractedEvidence> {
    // Ensure the Attestation report is properly signed by the platform and that it includes the
    // root public key used in the DICE chain.
    {
        let tee_certificate = match endorsements.r#type.as_ref().context("no endorsements")? {
            endorsements::Type::OakRestrictedKernel(endorsements) => endorsements
                .root_layer
                .as_ref()
                .context("no root layer endorsements")?
                .tee_certificate
                .as_ref(),
            endorsements::Type::OakContainers(endorsements) => endorsements
                .root_layer
                .as_ref()
                .context("no root layer endorsements")?
                .tee_certificate
                .as_ref(),
            endorsements::Type::Cb(endorsements) => endorsements
                .root_layer
                .as_ref()
                .context("no root layer endorsements")?
                .tee_certificate
                .as_ref(),
        };
        let root_layer = evidence
            .root_layer
            .as_ref()
            .context("no root layer evidence")?;
        verify_root_attestation_signature(now_utc_millis, root_layer, tee_certificate)?;
    };

    // Ensure the DICE chain signatures are valid and extract the measurements, public keys and
    // other attestation-related data from the DICE chain.
    let extracted_evidence = verify_dice_chain(evidence).context("invalid DICE chain")?;
    #[cfg(feature = "std")]
    println!("✅ DICE chain is valid.",);

    // Ensure the extracted measurements match the endorsements.
    match (
        endorsements.r#type.as_ref(),
        reference_values.r#type.as_ref(),
        extracted_evidence.evidence_values.as_ref(),
    ) {
        (
            Some(endorsements::Type::OakRestrictedKernel(ends)),
            Some(reference_values::Type::OakRestrictedKernel(rvs)),
            Some(EvidenceValues::OakRestrictedKernel(values)),
        ) => verify_oak_restricted_kernel(now_utc_millis, values, ends, rvs),
        (
            Some(endorsements::Type::OakContainers(ends)),
            Some(reference_values::Type::OakContainers(rvs)),
            Some(EvidenceValues::OakContainers(values)),
        ) => verify_oak_containers(now_utc_millis, values, ends, rvs),
        (
            Some(endorsements::Type::Cb(ends)),
            Some(reference_values::Type::Cb(rvs)),
            Some(EvidenceValues::Cb(values)),
        ) => verify_cb(now_utc_millis, values, ends, rvs),
        // Evidence, endorsements and reference values must exist and reflect the same chain type.
        (None, _, _) => anyhow::bail!("Endorsements are empty"),
        (_, None, _) => anyhow::bail!("Reference values are empty"),
        (_, _, None) => anyhow::bail!("Extracted evidence values are empty"),
        (Some(_), Some(_), Some(_)) => {
            anyhow::bail!("Mismatch between evidence, endorsements and reference values")
        }
    }?;

    Ok(extracted_evidence)
}

/// Verifies signatures of the certificates in the DICE chain and extracts the evidence values from
/// the certificates if the verification is successful.
pub fn verify_dice_chain(evidence: &Evidence) -> anyhow::Result<ExtractedEvidence> {
    let root_layer_verifying_key = {
        let cose_key = {
            let root_layer = evidence
                .root_layer
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("no root layer evidence"))?;
            CoseKey::from_slice(&root_layer.eca_public_key).map_err(|_cose_err| {
                anyhow::anyhow!("couldn't deserialize root layer public key")
            })?
        };
        cose_key_to_verifying_key(&cose_key).map_err(|msg| anyhow::anyhow!(msg))?
    };

    // Sequentially verify the layers, eventually retrieving the verifying key of the last layer.
    let last_layer_verifying_key = evidence.layers.iter().enumerate().try_fold(
        root_layer_verifying_key,
        |previous_layer_verifying_key, (index, current_layer)| {
            let cert = coset::CoseSign1::from_slice(&current_layer.eca_certificate)
                .map_err(|_cose_err| anyhow::anyhow!("could not parse certificate"))?;
            cert.verify_signature(ADDITIONAL_DATA, |signature, contents| {
                let sig = Signature::from_slice(signature)?;
                previous_layer_verifying_key.verify(contents, &sig)
            })
            .map_err(|error| anyhow::anyhow!(error))?;
            #[cfg(feature = "std")]
            println!(
                "✅ layer {} is signed by the previous layer.",
                // given there's a seperate root layer, we start the index at 1
                index + 1
            );
            let payload = cert
                .payload
                .ok_or_else(|| anyhow::anyhow!("no cert payload"))?;
            let claims = ClaimsSet::from_slice(&payload)
                .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))?;
            let cose_key =
                get_public_key_from_claims_set(&claims).map_err(|msg| anyhow::anyhow!(msg))?;
            cose_key_to_verifying_key(&cose_key).map_err(|msg| anyhow::anyhow!(msg))
        },
    )?;

    // Finally, use the last layer's verification key to verify the application keys.
    {
        let appl_keys = evidence
            .application_keys
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no application keys in evidence"))?;

        // Verify encryption certificate.
        let encryption_cert =
            coset::CoseSign1::from_slice(&appl_keys.encryption_public_key_certificate)
                .map_err(|_cose_err| anyhow::anyhow!("could not parse encryption certificate"))?;
        encryption_cert
            .verify_signature(ADDITIONAL_DATA, |signature, contents| {
                let sig = Signature::from_slice(signature)?;
                last_layer_verifying_key.verify(contents, &sig)
            })
            .map_err(|error| anyhow::anyhow!(error))?;

        // Verify signing certificate.
        let signing_cert = coset::CoseSign1::from_slice(&appl_keys.signing_public_key_certificate)
            .map_err(|_cose_err| anyhow::anyhow!("could not parse encryption certificate"))?;
        signing_cert
            .verify_signature(ADDITIONAL_DATA, |signature, contents| {
                let sig = Signature::from_slice(signature)?;
                last_layer_verifying_key.verify(contents, &sig)
            })
            .map_err(|error| anyhow::anyhow!(error))?;
    }

    println!("✅ application keys are signed by the previous layer",);

    extract_evidence(evidence)
}

/// Validates the values extracted from the evidence against the reference values and endorsements
/// for Oak Restricted Kernel applications.
fn verify_oak_restricted_kernel(
    now_utc_millis: i64,
    values: &OakRestrictedKernelData,
    endorsements: &OakRestrictedKernelEndorsements,
    reference_values: &OakRestrictedKernelReferenceValues,
) -> anyhow::Result<()> {
    verify_root_layer(
        now_utc_millis,
        values
            .root_layer
            .as_ref()
            .context("no root layer evidence values")?,
        endorsements.root_layer.as_ref(),
        reference_values
            .root_layer
            .as_ref()
            .context("no root layer reference values")?,
    )
    .context("root layer verification failed")?;

    verify_kernel_layer(
        now_utc_millis,
        values
            .kernel_layer
            .as_ref()
            .context("no kernel layer evidence values")?,
        endorsements.kernel_layer.as_ref(),
        reference_values
            .kernel_layer
            .as_ref()
            .context("no kernel layer reference values")?,
    )
    .context("kernel layer verification failed")?;

    verify_application_layer(
        now_utc_millis,
        values
            .application_layer
            .as_ref()
            .context("no applications layer evidence values")?,
        endorsements.application_layer.as_ref(),
        reference_values
            .application_layer
            .as_ref()
            .context("no application layer reference values")?,
    )
    .context("application layer verification failed")
}

/// Validates the values extracted from the evidence against the reference values and endorsements
/// for Oak Restricted Containers applications.
fn verify_oak_containers(
    now_utc_millis: i64,
    values: &OakContainersData,
    endorsements: &OakContainersEndorsements,
    reference_values: &OakContainersReferenceValues,
) -> anyhow::Result<()> {
    verify_root_layer(
        now_utc_millis,
        values
            .root_layer
            .as_ref()
            .context("no root layer evidence values")?,
        endorsements.root_layer.as_ref(),
        reference_values
            .root_layer
            .as_ref()
            .context("no root layer reference values")?,
    )
    .context("root layer verification failed")?;

    verify_kernel_layer(
        now_utc_millis,
        values
            .kernel_layer
            .as_ref()
            .context("no kernel layer evidence values")?,
        endorsements.kernel_layer.as_ref(),
        reference_values
            .kernel_layer
            .as_ref()
            .context("no kernel layer reference values")?,
    )
    .context("kernel layer verification failed")?;

    verify_system_layer(
        now_utc_millis,
        values
            .system_layer
            .as_ref()
            .context("no system layer evidence values")?,
        endorsements.system_layer.as_ref(),
        reference_values
            .system_layer
            .as_ref()
            .context("no system layer reference values")?,
    )
    .context("system layer verification failed")?;

    verify_container_layer(
        now_utc_millis,
        values
            .container_layer
            .as_ref()
            .context("no container layer evidence values")?,
        endorsements.container_layer.as_ref(),
        reference_values
            .container_layer
            .as_ref()
            .context("no container layer reference values")?,
    )
    .context("container layer verification failed")
}

/// Validates the values extracted from the evidence against the reference values and endorsements
/// for CB workloads.
fn verify_cb(
    now_utc_millis: i64,
    values: &CbData,
    endorsements: &CbEndorsements,
    reference_values: &CbReferenceValues,
) -> anyhow::Result<()> {
    verify_root_layer(
        now_utc_millis,
        values
            .root_layer
            .as_ref()
            .context("no root layer evidence values")?,
        endorsements.root_layer.as_ref(),
        reference_values
            .root_layer
            .as_ref()
            .context("no root layer reference values")?,
    )
    .context("root layer verification failed")?;

    anyhow::bail!("needs more implementation")
}

/// Verifies the AMD SEV attestation report.
fn verify_amd_sev_attestation_report(
    attestation_report_values: &AmdAttestationReport,
    reference_values: &AmdSevReferenceValues,
) -> anyhow::Result<()> {
    if !reference_values.allow_debug && attestation_report_values.debug {
        anyhow::bail!("debug mode not allowed");
    }

    if reference_values
        .firmware_version
        .as_ref()
        .is_some_and(|a| !a.values.is_empty())
    {
        anyhow::bail!("firmware version check needs implementation");
    }

    Ok(())
}

/// Verifies the Intel TDX attestation report.
fn verify_intel_tdx_attestation_report(
    _attestation_report_values: &IntelTdxAttestationReport,
    _reference_values: &IntelTdxReferenceValues,
) -> anyhow::Result<()> {
    anyhow::bail!("needs implementation")
}

/// Verifies a fake attestation report.
fn verify_fake_attestation_report(
    _attestation_report_values: &FakeAttestationReport,
    _reference_values: &InsecureReferenceValues,
) -> anyhow::Result<()> {
    Ok(())
}

/// Verifies the signature chain for the attestation report included in the root.
fn verify_root_attestation_signature(
    _now_utc_millis: i64,
    root_layer: &RootLayerEvidence,
    serialized_certificate: &[u8],
) -> anyhow::Result<()> {
    match root_layer.platform() {
        TeePlatform::Unspecified => anyhow::bail!("unspecified TEE platform"),
        TeePlatform::AmdSevSnp => {
            // We demand that product-specific ASK signs the VCEK.
            let vcek = Certificate::from_der(serialized_certificate)
                .map_err(|_err| anyhow::anyhow!("could not parse VCEK cert"))?;
            // Right now there are only Milan CPUs, so it is not urgent to code the
            // decision between Milan and Genoa which would appear here.
            let ask_milan = Certificate::from_pem(ASK_MILAN_CERT_PEM)
                .map_err(|_err| anyhow::anyhow!("could not parse ASK cert"))?;

            // TODO(#4747): user current date as part of VCEK verification.
            verify_cert_signature(&ask_milan, &vcek)?;

            let report = AttestationReport::ref_from(&root_layer.remote_attestation_report)
                .context("invalid AMD SEV-SNP attestation report")?;
            report.validate().map_err(|msg| anyhow::anyhow!(msg))?;

            // Ensure that the attestation report is signed by the VCEK public key.
            #[cfg(feature = "std")]
            verify_attestation_report_signature(&vcek, report)?;
            println!("✅ SEV-SNP Attestation Report is signed by AMD.");
            // Check that the root ECA public key for the DICE chain is bound to the attestation
            // report to ensure that the entire chain is valid.
            let expected = &hash_sha2_256(&root_layer.eca_public_key[..])[..];
            let actual = report.data.report_data;

            anyhow::ensure!(
                // The report data contains 64 bytes by default, but we only use the first 32 bytes
                // at the moment.
                expected.len() < actual.len() && expected == &actual[..expected.len()],
                "The root layer's ECA public key is not bound to the attestation report"
            );
            #[cfg(feature = "std")]
            println!("✅ SEV-SNP Attestation Report endorses root dice layer.");

            Ok(())
        }
        TeePlatform::IntelTdx => anyhow::bail!("not supported"),
        TeePlatform::None => Ok(()),
    }
}

/// Verifies the measurement values of the root layer containing the attestation report.
fn verify_root_layer(
    now_utc_millis: i64,
    values: &RootLayerData,
    endorsements: Option<&RootLayerEndorsements>,
    reference_values: &RootLayerReferenceValues,
) -> anyhow::Result<()> {
    match values.report.as_ref() {
        Some(Report::SevSnp(report_values)) => {
            // See b/327069120: We don't have the correct digest in the endorsement
            // to compare the stage0 measurement yet. This will fail UNLESS the stage0
            // reference value is set to `skip {}`.
            let measurement = RawDigest {
                sha2_384: report_values.initial_measurement.to_vec(),
                ..Default::default()
            };
            verify_measurement_digest(
                &measurement,
                now_utc_millis,
                endorsements.and_then(|value| value.stage0.as_ref()),
                reference_values
                    .amd_sev
                    .as_ref()
                    .context("AMD SEV-SNP reference values not found")?
                    .stage0
                    .as_ref()
                    .context("stage0 binary reference values not found")?,
            )?;
            println!("✅ initial memory measurement matches the evidence.",);
            verify_amd_sev_attestation_report(
                report_values,
                reference_values
                    .amd_sev
                    .as_ref()
                    .context("AMD SEV-SNP reference values not found")?,
            )
        }
        Some(Report::Tdx(report_values)) => verify_intel_tdx_attestation_report(
            report_values,
            reference_values
                .intel_tdx
                .as_ref()
                .context("Intel TDX reference values not found")?,
        ),
        Some(Report::Fake(report_values)) => verify_fake_attestation_report(
            report_values,
            reference_values
                .insecure
                .as_ref()
                .context("insecure reference values not found")?,
        ),
        None => Err(anyhow::anyhow!("no attestation report")),
    }
}

/// Verifies the measurement values of the kernel layer, which is common to both the  Oak Restricted
/// Kernel and Oak Containers setups.
fn verify_kernel_layer(
    now_utc_millis: i64,
    values: &KernelLayerData,
    endorsements: Option<&KernelLayerEndorsements>,
    reference_values: &KernelLayerReferenceValues,
) -> anyhow::Result<()> {
    verify_measurement_digest(
        values
            .kernel_image
            .as_ref()
            .context("no kernel image evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.kernel_image.as_ref()),
        reference_values
            .kernel_image
            .as_ref()
            .context("no kernel image reference value")?,
    )
    .context("kernel image failed verification")?;
    println!("✅ kernel image measurement matches the evidence.",);

    verify_measurement_digest(
        values
            .kernel_cmd_line
            .as_ref()
            .context("no kernel command-line evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.kernel_cmd_line.as_ref()),
        reference_values
            .kernel_cmd_line
            .as_ref()
            .context("no kernel command-line reference value")?,
    )
    .context("kernel command-line failed verification")?;

    verify_measurement_digest(
        values
            .kernel_setup_data
            .as_ref()
            .context("no setup data evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.kernel_setup_data.as_ref()),
        reference_values
            .kernel_setup_data
            .as_ref()
            .context("no kernel setup data reference value")?,
    )
    .context("kernel setup data failed verification")?;
    println!("✅ kernel setup data measurement matches the evidence.",);

    verify_measurement_digest(
        values
            .init_ram_fs
            .as_ref()
            .context("no initial RAM disk evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.init_ram_fs.as_ref()),
        reference_values
            .init_ram_fs
            .as_ref()
            .context("no initial RAM disk reference value")?,
    )
    .context("initial RAM disk failed verification")?;

    verify_measurement_digest(
        values
            .memory_map
            .as_ref()
            .context("no memory map evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.memory_map.as_ref()),
        reference_values
            .memory_map
            .as_ref()
            .context("no memory map reference value")?,
    )
    .context("memory map failed verification")?;

    verify_measurement_digest(
        values.acpi.as_ref().context("no ACPI evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.acpi.as_ref()),
        reference_values
            .acpi
            .as_ref()
            .context("no ACPI reference value")?,
    )
    .context("ACPI table building commands failed verification")
}

/// Verifies the measurement values of the system image layer for Oak Containers.
fn verify_system_layer(
    now_utc_millis: i64,
    values: &SystemLayerData,
    endorsements: Option<&SystemLayerEndorsements>,
    reference_values: &SystemLayerReferenceValues,
) -> anyhow::Result<()> {
    verify_measurement_digest(
        values
            .system_image
            .as_ref()
            .context("no system image evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.system_image.as_ref()),
        reference_values
            .system_image
            .as_ref()
            .context("no system image reference value")?,
    )
    .context("system image failed verification")
}

/// Verifies the measurement values of the application layer for Oak Restricted Kernel.
fn verify_application_layer(
    now_utc_millis: i64,
    values: &ApplicationLayerData,
    endorsements: Option<&ApplicationLayerEndorsements>,
    reference_values: &ApplicationLayerReferenceValues,
) -> anyhow::Result<()> {
    verify_measurement_digest(
        values.binary.as_ref().context("no binary evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.binary.as_ref()),
        reference_values
            .binary
            .as_ref()
            .context("application binary reference value")?,
    )
    .context("application binary failed verification")?;
    println!("✅ application measurement matches the evidence.",);

    verify_measurement_digest(
        values.config.as_ref().context("no config evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.configuration.as_ref()),
        reference_values
            .configuration
            .as_ref()
            .context("no configuration reference value")?,
    )
    .context("configuration failed verification")
}

/// Verifies the measurement values of the container layer for Oak Containers.
fn verify_container_layer(
    now_utc_millis: i64,
    values: &ContainerLayerData,
    endorsements: Option<&ContainerLayerEndorsements>,
    reference_values: &ContainerLayerReferenceValues,
) -> anyhow::Result<()> {
    verify_measurement_digest(
        values.bundle.as_ref().context("no bundle evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.binary.as_ref()),
        reference_values
            .binary
            .as_ref()
            .context("container bundle reference value")?,
    )
    .context("container bundle failed verification")?;

    verify_measurement_digest(
        values.config.as_ref().context("no config evidence value")?,
        now_utc_millis,
        endorsements.and_then(|value| value.configuration.as_ref()),
        reference_values
            .configuration
            .as_ref()
            .context("no configuration reference value")?,
    )
    .context("configuration failed verification")
}

/// Verifies the measurement digest value against a reference value and an optional transparent
/// release endorsement.
fn verify_measurement_digest(
    measurement: &RawDigest,
    now_utc_millis: i64,
    endorsement: Option<&TransparentReleaseEndorsement>,
    reference_value: &BinaryReferenceValue,
) -> anyhow::Result<()> {
    let actual = raw_to_hex_digest(measurement);
    match reference_value.r#type.as_ref() {
        Some(binary_reference_value::Type::Skip(_)) => Ok(()),
        Some(binary_reference_value::Type::Endorsement(public_keys)) => {
            let endorsement =
                endorsement.context("matching endorsement not found for reference value")?;
            verify_binary_endorsement(
                now_utc_millis,
                &endorsement.endorsement,
                &endorsement.rekor_log_entry,
                &public_keys.endorser_public_key,
                &public_keys.rekor_public_key,
            )?;
            let expected = get_digest(&parse_endorsement_statement(&endorsement.endorsement)?)?;
            verify_hex_digests(&actual, &expected)
        }
        Some(binary_reference_value::Type::Digests(expected_digests)) => {
            if expected_digests.digests.iter().any(|expected_digest| {
                let expected = raw_to_hex_digest(expected_digest);
                verify_hex_digests(&actual, &expected).is_ok()
            }) {
                Ok(())
            } else {
                Err(anyhow::anyhow!(
                    "measurement digest does not match any reference values"
                ))
            }
        }
        None => Err(anyhow::anyhow!("empty binary reference value")),
    }
}

fn verify_hex_digests(actual: &HexDigest, expected: &HexDigest) -> anyhow::Result<()> {
    match is_hex_digest_match(actual, expected) {
        MatchResult::SAME => Ok(()),
        MatchResult::DIFFERENT => Err(anyhow::anyhow!(
            "mismatched digests: expected={expected:?} actual={actual:?}",
        )),
        MatchResult::UNDECIDABLE => Err(anyhow::anyhow!("invalid digests")),
    }
}

struct ApplicationKeyValues {
    encryption_public_key: Vec<u8>,
    signing_public_key: Vec<u8>,
}

/// Extracts measurements, public keys and other attestation-related values from the evidence.
fn extract_evidence(evidence: &Evidence) -> anyhow::Result<ExtractedEvidence> {
    let evidence_values =
        Some(extract_evidence_values(evidence).context("couldn't extract evidence values")?);
    let ApplicationKeyValues {
        encryption_public_key,
        signing_public_key,
    } = extract_application_key_values(
        evidence
            .application_keys
            .as_ref()
            .context("no application keys")?,
    )
    .context("couldn't extract application key values")?;

    Ok(ExtractedEvidence {
        evidence_values,
        encryption_public_key,
        signing_public_key,
    })
}

/// Extracts the measurements and other attestation-related values from the evidence.
fn extract_evidence_values(evidence: &Evidence) -> anyhow::Result<EvidenceValues> {
    let root_layer = Some(extract_root_values(
        evidence
            .root_layer
            .as_ref()
            .context("no root layer evidence")?,
    )?);

    let final_layer_claims = &claims_set_from_serialized_cert(
        &evidence
            .application_keys
            .as_ref()
            .context("no application keys")?
            .encryption_public_key_certificate,
    )
    .context("couldn't parse final DICE layer certificate")?;

    // Determine the type of evidence from the claims in the certificate for the final.
    if let Ok(container_layer_data) = extract_container_layer_data(final_layer_claims) {
        match &evidence.layers[..] {
            [kernel_layer, system_layer] => {
                let kernel_layer = Some(
                    extract_kernel_values(
                        &claims_set_from_serialized_cert(&kernel_layer.eca_certificate)
                            .context("couldn't parse kernel DICE layer certificate")?,
                    )
                    .context("couldn't extract kernel values")?,
                );
                let system_layer = Some(
                    extract_system_layer_data(
                        &claims_set_from_serialized_cert(&system_layer.eca_certificate)
                            .context("couldn't parse system DICE layer certificate")?,
                    )
                    .context("couldn't extract system layer values")?,
                );

                let container_layer = Some(container_layer_data);
                Ok(EvidenceValues::OakContainers(OakContainersData {
                    root_layer,
                    kernel_layer,
                    system_layer,
                    container_layer,
                }))
            }
            _ => Err(anyhow::anyhow!(
                "incorrect number of DICE layers for Oak Containers"
            )),
        }
    } else if let Ok(application_layer_data) = extract_application_layer_data(final_layer_claims) {
        match &evidence.layers[..] {
            [kernel_layer] => {
                let kernel_layer = Some(
                    extract_kernel_values(
                        &claims_set_from_serialized_cert(&kernel_layer.eca_certificate)
                            .context("couldn't parse kernel DICE layer certificate")?,
                    )
                    .context("couldn't extract kernel values")?,
                );

                let application_layer = Some(application_layer_data);
                Ok(EvidenceValues::OakRestrictedKernel(
                    OakRestrictedKernelData {
                        root_layer,
                        kernel_layer,
                        application_layer,
                    },
                ))
            }
            _ => Err(anyhow::anyhow!(
                "incorrect number of DICE layers for Oak Containers"
            )),
        }
    } else {
        // Assume for now this is CB evidence until the CB fields are better defined.
        Ok(EvidenceValues::Cb(CbData { root_layer }))
    }
}

/// Extracts values from the attestation report.
fn extract_root_values(root_layer: &RootLayerEvidence) -> anyhow::Result<RootLayerData> {
    match root_layer.platform() {
        TeePlatform::Unspecified => Err(anyhow::anyhow!("unspecified TEE platform")),
        TeePlatform::AmdSevSnp => {
            let report = AttestationReport::ref_from(&root_layer.remote_attestation_report)
                .context("invalid AMD SEV-SNP attestation report")?;

            report.validate().map_err(|msg| anyhow::anyhow!(msg))?;

            let current_tcb = Some(TcbVersion {
                boot_loader: report.data.current_tcb.boot_loader.into(),
                tee: report.data.current_tcb.tee.into(),
                snp: report.data.current_tcb.snp.into(),
                microcode: report.data.current_tcb.microcode.into(),
            });
            let debug = report
                .has_debug_flag()
                .map_err(|error| anyhow::anyhow!(error))?;
            let hardware_id = report.data.chip_id.as_ref().to_vec();
            let initial_measurement = report.data.measurement.as_ref().to_vec();
            let report_data = report.data.report_data.as_ref().to_vec();

            Ok(RootLayerData {
                report: Some(Report::SevSnp(AmdAttestationReport {
                    current_tcb,
                    debug,
                    initial_measurement,
                    hardware_id,
                    report_data,
                })),
            })
        }
        TeePlatform::IntelTdx => Err(anyhow::anyhow!("not supported")),
        TeePlatform::None => {
            // We use an unsigned, mostly empty AMD SEV-SNP attestation report as a fake when not
            // running in a TEE.
            let report = AttestationReport::ref_from(&root_layer.remote_attestation_report)
                .context("invalid fake attestation report")?;

            report.validate().map_err(|msg| anyhow::anyhow!(msg))?;

            let report_data = report.data.report_data.as_ref().to_vec();

            Ok(RootLayerData {
                report: Some(Report::Fake(FakeAttestationReport { report_data })),
            })
        }
    }
}

/// Extracts the application public keys.
fn extract_application_key_values(
    application_keys: &ApplicationKeys,
) -> anyhow::Result<ApplicationKeyValues> {
    let encryption_claims =
        claims_set_from_serialized_cert(&application_keys.encryption_public_key_certificate[..])?;
    let encryption_cose_key =
        get_public_key_from_claims_set(&encryption_claims).map_err(|msg| anyhow::anyhow!(msg))?;
    let encryption_public_key =
        cose_key_to_hpke_public_key(&encryption_cose_key).map_err(|msg| anyhow::anyhow!(msg))?;

    let signing_claims =
        claims_set_from_serialized_cert(&application_keys.signing_public_key_certificate[..])?;
    let signing_cose_key: CoseKey =
        get_public_key_from_claims_set(&signing_claims).map_err(|msg| anyhow::anyhow!(msg))?;
    let signing_verifying_key =
        cose_key_to_verifying_key(&signing_cose_key).map_err(|msg| anyhow::anyhow!(msg))?;
    let signing_public_key = signing_verifying_key.to_sec1_bytes().to_vec();

    Ok(ApplicationKeyValues {
        encryption_public_key,
        signing_public_key,
    })
}

/// Extracts the measurement values for the kernel layer.
fn extract_kernel_values(claims: &ClaimsSet) -> anyhow::Result<KernelLayerData> {
    let values =
        extract_layer_data(claims, KERNEL_LAYER_ID).context("kernel layer ID not found")?;
    let kernel_image = Some(value_to_raw_digest(extract_value(
        values,
        KERNEL_MEASUREMENT_ID,
    )?)?);
    let kernel_cmd_line = Some(value_to_raw_digest(extract_value(
        values,
        KERNEL_COMMANDLINE_MEASUREMENT_ID,
    )?)?);
    let kernel_setup_data = Some(value_to_raw_digest(extract_value(
        values,
        SETUP_DATA_MEASUREMENT_ID,
    )?)?);
    let init_ram_fs = Some(value_to_raw_digest(extract_value(
        values,
        INITRD_MEASUREMENT_ID,
    )?)?);
    let memory_map = Some(value_to_raw_digest(extract_value(
        values,
        MEMORY_MAP_MEASUREMENT_ID,
    )?)?);
    let acpi = Some(value_to_raw_digest(extract_value(
        values,
        ACPI_MEASUREMENT_ID,
    )?)?);
    Ok(KernelLayerData {
        kernel_image,
        kernel_cmd_line,
        kernel_setup_data,
        init_ram_fs,
        memory_map,
        acpi,
    })
}

/// Extracts the measurement values for the system image layer.
fn extract_system_layer_data(claims: &ClaimsSet) -> anyhow::Result<SystemLayerData> {
    let values =
        extract_layer_data(claims, SYSTEM_IMAGE_LAYER_ID).context("system layer ID not found")?;
    let system_image = Some(value_to_raw_digest(extract_value(
        values,
        LAYER_2_CODE_MEASUREMENT_ID,
    )?)?);
    Ok(SystemLayerData { system_image })
}

/// Extracts the measurement values for the system image layer.
fn extract_container_layer_data(claims: &ClaimsSet) -> anyhow::Result<ContainerLayerData> {
    let values = extract_layer_data(claims, CONTAINER_IMAGE_LAYER_ID)
        .context("system layer ID not found")?;
    let bundle = Some(value_to_raw_digest(extract_value(
        values,
        LAYER_3_CODE_MEASUREMENT_ID,
    )?)?);
    let config = Some(value_to_raw_digest(extract_value(
        values,
        FINAL_LAYER_CONFIG_MEASUREMENT_ID,
    )?)?);
    Ok(ContainerLayerData { bundle, config })
}

/// Extracts the measurement values for the enclave application layer.
fn extract_application_layer_data(claims: &ClaimsSet) -> anyhow::Result<ApplicationLayerData> {
    let values = extract_layer_data(claims, ENCLAVE_APPLICATION_LAYER_ID)
        .context("system layer ID not found")?;
    let binary = Some(value_to_raw_digest(extract_value(
        values,
        LAYER_2_CODE_MEASUREMENT_ID,
    )?)?);
    let config = Some(value_to_raw_digest(extract_value(
        values,
        FINAL_LAYER_CONFIG_MEASUREMENT_ID,
    )?)?);
    Ok(ApplicationLayerData { binary, config })
}

/// Parses the CBOR map from a serialized certificate.
fn claims_set_from_serialized_cert(slice: &[u8]) -> anyhow::Result<ClaimsSet> {
    let cert = coset::CoseSign1::from_slice(slice)
        .map_err(|_cose_err| anyhow::anyhow!("could not parse certificate"))?;
    let payload = cert
        .payload
        .ok_or_else(|| anyhow::anyhow!("no signing cert payload"))?;
    ClaimsSet::from_slice(&payload)
        .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))
}

/// Extracts the claim that contains the values for the specified layer.
fn extract_layer_data(claims: &ClaimsSet, layer_id: i64) -> anyhow::Result<&Vec<(Value, Value)>> {
    let target = RegisteredLabelWithPrivate::PrivateUse(layer_id);
    claims
        .rest
        .iter()
        .find_map(|(label, value)| {
            if let Value::Map(map) = value
                && label == &target
            {
                Some(map)
            } else {
                None
            }
        })
        .context("couldn't find layer values")
}

/// Extracts a value for the label from the layer's mapping between labels and values.
fn extract_value(values: &[(Value, Value)], label_id: i64) -> anyhow::Result<&Value> {
    let target_key = Value::Integer(label_id.into());
    values
        .iter()
        .find_map(|(key, value)| {
            if key == &target_key {
                Some(value)
            } else {
                None
            }
        })
        .context("couldn't find measurement")
}

/// Extracts the individual digests from a value that represents a set of digests.
fn value_to_raw_digest(value: &Value) -> anyhow::Result<RawDigest> {
    if let Value::Map(map) = value {
        let mut result = RawDigest::default();
        for (key, digest) in map.iter() {
            if let Value::Bytes(bytes) = digest {
                if key == &Value::Integer(SHA2_256_ID.into()) {
                    result.sha2_256 = bytes.to_vec();
                } else {
                    anyhow::bail!("digest is not a byte array");
                }
            } else {
                anyhow::bail!("digest is not a byte array");
            }
        }
        return Ok(result);
    }
    Err(anyhow::anyhow!("value is not a map of digests"))
}
