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

use alloc::format;

use anyhow::Context;
use coset::{cwt::ClaimsSet, CborSerializable, CoseKey};
use ecdsa::{signature::Verifier, Signature};
use oak_dice::cert::{cose_key_to_verifying_key, get_public_key_from_claims_set};
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results::Status, endorsements, expected_digests, expected_values,
        extracted_evidence::EvidenceValues, root_layer_data::Report, text_expected_value,
        AmdAttestationReport, AmdSevExpectedValues, ApplicationLayerData,
        ApplicationLayerExpectedValues, AttestationResults, CbData, CbExpectedValues,
        ContainerLayerData, ContainerLayerExpectedValues, Endorsements, EventData,
        EventExpectedValues, EventLog, Evidence, ExpectedDigests, ExpectedValues,
        ExtractedEvidence, InsecureExpectedValues, IntelTdxAttestationReport,
        IntelTdxExpectedValues, KernelLayerData, KernelLayerExpectedValues, LayerEvidence,
        OakContainersData, OakContainersExpectedValues, OakRestrictedKernelData,
        OakRestrictedKernelExpectedValues, ReferenceValues, RootLayerData, RootLayerEvidence,
        RootLayerExpectedValues, SystemLayerData, SystemLayerExpectedValues, TeePlatform,
        TextExpectedValue,
    },
    RawDigest,
};
use oak_sev_snp_attestation_report::AttestationReport;
#[cfg(feature = "regex")]
use regex_lite::Regex;
use x509_cert::{
    der::{Decode, DecodePem},
    Certificate,
};
use zerocopy::FromBytes;

use crate::{
    amd::{product_name, verify_attestation_report_signature, verify_cert_signature},
    expect::get_expected_values,
    extract::{
        claims_set_from_serialized_cert, extract_application_key_values, extract_event_data,
        extract_evidence_values, ApplicationKeyValues,
    },
    util::{hash_sha2_256, is_raw_digest_match},
};

// We don't use additional authenticated data.
const ADDITIONAL_DATA: &[u8] = b"";

pub fn to_attestation_results(
    verify_result: &anyhow::Result<ExtractedEvidence>,
) -> AttestationResults {
    match verify_result {
        #[allow(deprecated)]
        Ok(extracted_evidence) => AttestationResults {
            status: Status::Success.into(),
            encryption_public_key: extracted_evidence.encryption_public_key.clone(),
            signing_public_key: extracted_evidence.signing_public_key.clone(),
            extracted_evidence: Some(extracted_evidence.clone()),
            ..Default::default()
        },
        Err(err) => AttestationResults {
            status: Status::GenericFailure.into(),
            reason: format!("{:#?}", err),
            ..Default::default()
        },
    }
}

/// Verifies entire setup by forwarding to individual setup types.
///
/// This just fetches expected values using [`expect::get_expected_values`],
/// and then call [`verify_with_expected_values`] providing those values.
///
/// If you'd like to cache and reuse the values, call those two methods
/// independently, and cache the results of the first.
pub fn verify(
    now_utc_millis: i64,
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> anyhow::Result<ExtractedEvidence> {
    let expected_values = get_expected_values(now_utc_millis, endorsements, reference_values)
        .context("getting expected values")?;

    verify_with_expected_values(now_utc_millis, evidence, endorsements, &expected_values)
}

/// Verifies entire setup by forwarding to individual setup types.
pub fn verify_with_expected_values(
    now_utc_millis: i64,
    evidence: &Evidence,
    endorsements: &Endorsements,
    expected_values: &ExpectedValues,
) -> anyhow::Result<ExtractedEvidence> {
    // Ensure the Attestation report is properly signed by the platform and that it
    // includes the root public key used in the DICE chain.
    {
        let tee_certificate: &[u8] =
            match endorsements.r#type.as_ref().context("no endorsements")? {
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
        let root_layer = evidence.root_layer.as_ref().context("no root layer evidence")?;
        verify_root_attestation_signature(now_utc_millis, root_layer, tee_certificate)
            .context("verifying root signature")?;
    };

    // Ensure the DICE chain signatures are valid and extract the measurements,
    // public keys and other attestation-related data from the DICE chain.
    let extracted_evidence = verify_dice_chain(evidence).context("invalid DICE chain")?;

    compare_expected_values(&extracted_evidence, expected_values)
        .context("comparing expected values to evidence")?;

    Ok(extracted_evidence)
}

fn compare_expected_values(
    extracted_evidence: &ExtractedEvidence,
    expected_values: &ExpectedValues,
) -> anyhow::Result<()> {
    match (extracted_evidence.evidence_values.as_ref(), expected_values.r#type.as_ref()) {
        (
            Some(EvidenceValues::OakRestrictedKernel(values)),
            Some(expected_values::Type::OakRestrictedKernel(expected)),
        ) => compare_oak_restricted_kernel_measurement_digests(values, expected),
        (
            Some(EvidenceValues::OakContainers(values)),
            Some(expected_values::Type::OakContainers(expected)),
        ) => compare_oak_containers_measurement_digests(values, expected),
        (Some(EvidenceValues::Cb(values)), Some(expected_values::Type::Cb(expected))) => {
            compare_cb_measurement_digests(values, expected)
        }
        // Evidence, endorsements and reference values must exist and reflect the same chain type.
        (None, _) => anyhow::bail!("Reference values are empty"),
        (_, None) => anyhow::bail!("Expected values are empty"),
        (Some(_), Some(_)) => {
            anyhow::bail!("Mismatch between evidence, endorsements and reference values")
        }
    }
}

/// Verifies signatures of the certificates in the DICE chain and extracts the
/// evidence values from the certificates if the verification is successful.
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

    // Sequentially verify the layers, eventually retrieving the verifying key of
    // the last layer.
    let last_layer_verifying_key = evidence
        .layers
        .iter()
        .try_fold(root_layer_verifying_key, |previous_layer_verifying_key, current_layer| {
            let cert = coset::CoseSign1::from_slice(&current_layer.eca_certificate)
                .map_err(|_cose_err| anyhow::anyhow!("could not parse certificate"))?;
            cert.verify_signature(ADDITIONAL_DATA, |signature, contents| {
                let sig = Signature::from_slice(signature)?;
                previous_layer_verifying_key.verify(contents, &sig)
            })
            .map_err(|error| anyhow::anyhow!(error))?;
            let payload = cert.payload.ok_or_else(|| anyhow::anyhow!("no cert payload"))?;
            let claims = ClaimsSet::from_slice(&payload)
                .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))?;
            let cose_key = get_public_key_from_claims_set(&claims)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("getting pk from claims")?;
            cose_key_to_verifying_key(&cose_key)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("converting cose key")
        })
        .context("getting last layer key")?;

    // Finally, use the last layer's verification key to verify the application
    // keys.
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
            .map_err(|error| anyhow::anyhow!(error))
            .context("failed to verify CWT signature")?;

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

    // Verify the event log claim for this layer if it exists. This is done for all
    // layers here, since the event log is tied uniquely closely to the DICE chain.
    if let Some(event_log) = &evidence.event_log {
        validate_that_event_log_is_captured_in_dice_layers(event_log, &evidence.layers)
            .context("events in log do not match the digests in the dice chain")?
    }
    extract_evidence(evidence)
}

/// Extracts attestation-related values without verificaiton.
///
/// Extracts measurements, public keys, and other attestation-related values
/// from the evidence without verifying it. For most usecases, this function
/// should not be used. Instead use the [`verify`] function, which verifies the
/// attestation and only returns evidence upon successful verification. Hence
/// marked as dangerous.
pub fn extract_evidence(evidence: &Evidence) -> anyhow::Result<ExtractedEvidence> {
    let evidence_values =
        Some(extract_evidence_values(evidence).context("couldn't extract evidence values")?);
    let ApplicationKeyValues { encryption_public_key, signing_public_key } =
        extract_application_key_values(
            evidence.application_keys.as_ref().context("no application keys")?,
        )
        .context("couldn't extract application key values")?;

    Ok(ExtractedEvidence { evidence_values, encryption_public_key, signing_public_key })
}

/// Validates that the digest of the events captured in the event log are
/// correctly described in the claims of the associated dice layers.
fn validate_that_event_log_is_captured_in_dice_layers(
    event_log: &EventLog,
    dice_layers: &[LayerEvidence],
) -> anyhow::Result<()> {
    dice_layers.iter().zip(event_log.encoded_events.iter()).try_for_each(
        |(current_layer, encoded_event)| {
            let event_digest = {
                let claims = claims_set_from_serialized_cert(&current_layer.eca_certificate)
                    .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))?;
                extract_event_data(&claims)
                    .context("couldn't extract event claim")?
                    .event
                    .context("Missing event")?
            };
            let actual_event_hash = &<sha2::Sha256 as sha2::Digest>::digest(encoded_event).to_vec();
            if actual_event_hash != &event_digest.sha2_256 {
                Err(anyhow::anyhow!("event log hash mismatch"))
            } else {
                Ok(())
            }
        },
    )
}

/// Validates the values extracted from the evidence against the reference
/// values and endorsements for Oak Restricted Kernel applications.
fn compare_oak_restricted_kernel_measurement_digests(
    values: &OakRestrictedKernelData,
    expected: &OakRestrictedKernelExpectedValues,
) -> anyhow::Result<()> {
    compare_root_layer_measurement_digests(
        values.root_layer.as_ref().context("no root layer evidence values")?,
        expected.root_layer.as_ref().context("no root layer expected values")?,
    )
    .context("comparing root layer values")?;

    compare_kernel_layer_measurement_digests(
        values.kernel_layer.as_ref().context("no kernel layer evidence values")?,
        expected.kernel_layer.as_ref().context("no kernel layer expected values")?,
    )
    .context("comparing kernel layer values")?;

    compare_application_layer_measurement_digests(
        values.application_layer.as_ref().context("no applications layer evidence values")?,
        expected.application_layer.as_ref().context("no application layer expected values")?,
    )
    .context("comparing application layer values")
}

/// Validates the values extracted from the evidence against the reference
/// values and endorsements for Oak Restricted Containers applications.
fn compare_oak_containers_measurement_digests(
    values: &OakContainersData,
    expected: &OakContainersExpectedValues,
) -> anyhow::Result<()> {
    compare_root_layer_measurement_digests(
        values.root_layer.as_ref().context("no root layer evidence values")?,
        expected.root_layer.as_ref().context("no root layer expected values")?,
    )
    .context("comparing root layer digests")?;

    compare_kernel_layer_measurement_digests(
        values.kernel_layer.as_ref().context("no kernel layer evidence values")?,
        expected.kernel_layer.as_ref().context("no kernel layer expected_values")?,
    )
    .context("comparing kernel layer digests")?;

    compare_system_layer_measurement_digests(
        values.system_layer.as_ref().context("no system layer evidence values")?,
        expected.system_layer.as_ref().context("no system layer expected_values")?,
    )
    .context("comparing system layer digests")?;

    compare_container_layer_measurement_digests(
        values.container_layer.as_ref().context("no container layer evidence values")?,
        expected.container_layer.as_ref().context("no system layer expected_values")?,
    )
    .context("comparing container layer digests")
}

/// Validates the values extracted from the evidence against the reference
/// values and endorsements for CB workloads.
fn compare_cb_measurement_digests(
    values: &CbData,
    expected: &CbExpectedValues,
) -> anyhow::Result<()> {
    compare_root_layer_measurement_digests(
        values.root_layer.as_ref().context("no root layer evidence values")?,
        expected.root_layer.as_ref().context("no root layer expected values")?,
    )
    .context("root layer verification failed")?;

    compare_event_measurement_digests(
        values.kernel_layer.as_ref().context("no kernel layer evidence values")?,
        expected.kernel_layer.as_ref().context("no kernel layer expected_values")?,
    )
    .context("kernel layer verification failed")?;

    compare_event_measurement_digests(
        values.system_layer.as_ref().context("no system layer evidence values")?,
        expected.system_layer.as_ref().context("no system layer expected_values")?,
    )
    .context("system layer verification failed")?;

    compare_event_measurement_digests(
        values.application_layer.as_ref().context("no application layer evidence values")?,
        expected.application_layer.as_ref().context("no application layer expected_values")?,
    )
    .context("application layer verification failed")
}

/// Verifies the AMD SEV attestation report.
fn verify_amd_sev_attestation_report(
    attestation_report_values: &AmdAttestationReport,
    expected_values: &AmdSevExpectedValues,
) -> anyhow::Result<()> {
    // Stage 0 only destroys VMPCK0, so we only trust attestation reports that were
    // generated in VMPL0.
    anyhow::ensure!(
        attestation_report_values.vmpl == 0,
        "attestation report was not generated from VMPL {}, not VMPL 0",
        attestation_report_values.vmpl
    );

    if !expected_values.allow_debug && attestation_report_values.debug {
        anyhow::bail!("debug mode not allowed");
    }

    match (
        expected_values.min_tcb_version.as_ref(),
        attestation_report_values.reported_tcb.as_ref(),
    ) {
        (Some(min_tcb_version), Some(reported_tcb_version)) => {
            anyhow::ensure!(
                reported_tcb_version.boot_loader >= min_tcb_version.boot_loader,
                format!(
                    "unsupported boot loader version in the reported TCB: {}",
                    reported_tcb_version.boot_loader
                )
            );
            anyhow::ensure!(
                reported_tcb_version.tee >= min_tcb_version.tee,
                format!(
                    "unsupported tee version in the reported TCB: {}",
                    reported_tcb_version.tee
                )
            );
            anyhow::ensure!(
                reported_tcb_version.snp >= min_tcb_version.snp,
                format!(
                    "unsupported snp version in the reported TCB: {}",
                    reported_tcb_version.snp
                )
            );
            anyhow::ensure!(
                reported_tcb_version.microcode >= min_tcb_version.microcode,
                format!(
                    "unsupported microcode version in the reported TCB: {}",
                    reported_tcb_version.microcode
                )
            );
        }
        (Some(_), None) => anyhow::bail!("no reported TCB version in the attestation report"),
        (None, _) => anyhow::bail!("no min TCB version reference value"),
    }

    Ok(())
}

/// Verifies the Intel TDX attestation report.
fn verify_intel_tdx_attestation_report(
    _attestation_report_values: &IntelTdxAttestationReport,
    _expected_values: &IntelTdxExpectedValues,
) -> anyhow::Result<()> {
    anyhow::bail!("needs implementation")
}

/// Verifies insecure attestation.
fn verify_insecure(_expected_values: &InsecureExpectedValues) -> anyhow::Result<()> {
    Ok(())
}

const ASK_MILAN_CERT_PEM: &str = include_str!("../data/ask_milan.pem");
const ASK_GENOA_CERT_PEM: &str = include_str!("../data/ask_genoa.pem");

/// Verifies the signature chain for the attestation report included in the
/// root.
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

            let ask = if product_name(&vcek)?.contains("Milan") {
                Certificate::from_pem(ASK_MILAN_CERT_PEM)
                    .map_err(|_err| anyhow::anyhow!("could not parse Milan ASK cert"))?
            } else if product_name(&vcek)?.contains("Genoa") {
                Certificate::from_pem(ASK_GENOA_CERT_PEM)
                    .map_err(|_err| anyhow::anyhow!("could not parse Genoa ASK cert"))?
            } else {
                anyhow::bail!("unsupported AMD product");
            };

            // TODO(#4747): user current date as part of VCEK verification.
            verify_cert_signature(&ask, &vcek).context("verifying vcek cert")?;

            let report = AttestationReport::ref_from(&root_layer.remote_attestation_report)
                .context("invalid AMD SEV-SNP attestation report")?;
            report.validate().map_err(|msg| anyhow::anyhow!(msg))?;

            // Ensure that the attestation report is signed by the VCEK public key.
            verify_attestation_report_signature(&vcek, report)
                .context("verifying attestation report signature")?;

            // Check that the root ECA public key for the DICE chain is bound to the
            // attestation report to ensure that the entire chain is valid.
            let expected = &hash_sha2_256(&root_layer.eca_public_key[..])[..];
            let actual = report.data.report_data;

            anyhow::ensure!(
                // The report data contains 64 bytes by default, but we only use the first 32 bytes
                // at the moment.
                expected.len() < actual.len() && expected == &actual[..expected.len()],
                "The root layer's ECA public key is not bound to the attestation report"
            );

            Ok(())
        }
        TeePlatform::IntelTdx => anyhow::bail!("not supported"),
        TeePlatform::None => Ok(()),
    }
}

fn compare_root_layer_measurement_digests(
    values: &RootLayerData,
    expected_values: &RootLayerExpectedValues,
) -> anyhow::Result<()> {
    match (
        values.report.as_ref(),
        expected_values.amd_sev.as_ref(),
        expected_values.intel_tdx.as_ref(),
        expected_values.insecure.as_ref(),
    ) {
        (Some(Report::SevSnp(report_values)), Some(amd_sev_values), _, _) => {
            let measurement = RawDigest {
                sha2_384: report_values.initial_measurement.to_vec(),
                ..Default::default()
            };
            compare_measurement_digest(
                &measurement,
                amd_sev_values
                    .stage0_expected
                    .as_ref()
                    .context("no stage0 expected value provided")?,
            )
            .context("stage0 measurement values failed verification")?;
            verify_amd_sev_attestation_report(report_values, amd_sev_values)
        }
        (Some(Report::Tdx(report_values)), _, Some(intel_tdx_values), _) => {
            verify_intel_tdx_attestation_report(report_values, intel_tdx_values)
        }
        (_, _, _, Some(insecure_values)) => {
            verify_insecure(insecure_values).context("insecure root layer verification failed")
        }
        (Some(Report::Fake(_)), _, _, None) => {
            Err(anyhow::anyhow!("unexpected insecure attestation report"))
        }
        (None, _, _, _) => Err(anyhow::anyhow!("no attestation report")),
        (_, _, _, _) => Err(anyhow::anyhow!(
            "invalid combination of root layer reference values and endorsed evidence"
        )),
    }
}

/// Verifies the measurement values of the kernel layer, which is common to both
/// the Oak Restricted Kernel and Oak Containers setups.
pub(crate) fn compare_kernel_layer_measurement_digests(
    values: &KernelLayerData,
    expected: &KernelLayerExpectedValues,
) -> anyhow::Result<()> {
    let expected_kernel_values = expected.kernel.as_ref().context("no kernel expected values")?;

    compare_measurement_digest(
        values.kernel_image.as_ref().context("no kernel evidence value")?,
        expected_kernel_values
            .image
            .as_ref()
            .context("expected values contained no image digests")?,
    )
    .context("kernel image failed verification")?;

    compare_measurement_digest(
        values.kernel_setup_data.as_ref().context("no kernel setup data evidence value")?,
        expected_kernel_values
            .setup_data
            .as_ref()
            .context("expected values contained no setup_data digests")?,
    )
    .context("kernel setup data failed verification")?;

    // TODO: b/331252282 - Remove temporary workaround for cmd line.
    match (&values.kernel_raw_cmd_line, &expected.kernel_cmd_line_text) {
        // We support the skipped value, whether the kernel cmd line text is valid or not.
        // Skipping is a way to work around the cmd line length limit.
        (_, Some(TextExpectedValue { r#type: Some(text_expected_value::Type::Skipped(_)) })) => {
            Ok(())
        }

        // If a kernel cmd line is provided, it must be shorter than 256 bytes.
        (Some(kernel_raw_cmd_line), Some(expected)) if kernel_raw_cmd_line.len() < 256 => {
            compare_text_value(kernel_raw_cmd_line.as_str(), expected)
        }
        _ => Err(anyhow::anyhow!("No valid kernel_raw_cmd_line provided")),
    }?;

    compare_measurement_digest(
        values.init_ram_fs.as_ref().context("no initramfs value provided")?,
        expected.init_ram_fs.as_ref().context("no initramfs expected value provided")?,
    )
    .context("initramfs value failed verification")?;
    compare_measurement_digest(
        values.memory_map.as_ref().context("no memory_map value provided")?,
        expected.memory_map.as_ref().context("no memory_map expected value provided")?,
    )
    .context("memory_map value failed verification")?;
    compare_measurement_digest(
        values.acpi.as_ref().context("no ACPI table value provided")?,
        expected.acpi.as_ref().context("no ACPI table expected value provided")?,
    )
    .context("ACPI table value failed verification")
}

pub(crate) fn compare_event_measurement_digests(
    values: &EventData,
    expected: &EventExpectedValues,
) -> anyhow::Result<()> {
    compare_measurement_digest(
        values.event.as_ref().context("no event evidence value")?,
        expected.event.as_ref().context("no event image value")?,
    )
    .context("event failed verification")
}

pub(crate) fn compare_system_layer_measurement_digests(
    values: &SystemLayerData,
    expected: &SystemLayerExpectedValues,
) -> anyhow::Result<()> {
    compare_measurement_digest(
        values.system_image.as_ref().context("no system image evidence value")?,
        expected.system_image.as_ref().context("no expected system image value")?,
    )
    .context("system layer system image failed verification")
}

pub(crate) fn compare_application_layer_measurement_digests(
    values: &ApplicationLayerData,
    expected: &ApplicationLayerExpectedValues,
) -> anyhow::Result<()> {
    compare_measurement_digest(
        values.binary.as_ref().context("no binary evidence value")?,
        expected.binary.as_ref().context("no expected binary value")?,
    )
    .context("application layer binary failed verification")?;
    compare_measurement_digest(
        values.config.as_ref().context("no config evidence value")?,
        expected.configuration.as_ref().context("no expected config value")?,
    )
    .context("application layer config failed verification")
}

pub(crate) fn compare_container_layer_measurement_digests(
    values: &ContainerLayerData,
    expected: &ContainerLayerExpectedValues,
) -> anyhow::Result<()> {
    compare_measurement_digest(
        values.bundle.as_ref().context("no bundle evidence value")?,
        expected.bundle.as_ref().context("no expected bundle value")?,
    )
    .context("container bundle failed verification")?;
    compare_measurement_digest(
        values.config.as_ref().context("no config evidence value")?,
        expected.config.as_ref().context("no expected config value")?,
    )
    .context("container config failed verification")
}

/// Verifies the measurement digest value against a reference value and
/// the expected digests calculated from endorsements and reference values.
fn compare_measurement_digest(
    measurement: &RawDigest,
    expected: &ExpectedDigests,
) -> anyhow::Result<()> {
    match expected.r#type.as_ref() {
        Some(expected_digests::Type::Skipped(_)) => Ok(()),
        Some(expected_digests::Type::Digests(digests)) => digests
            .digests
            .iter()
            .find(|expected| is_raw_digest_match(measurement, expected).is_ok())
            .map(|_| ())
            .ok_or(anyhow::anyhow!(
                "measurement digest {:?} does not match any reference values",
                measurement
            )),
        None => Err(anyhow::anyhow!("empty expected value")),
    }
}

fn compare_text_value(actual: &str, expected: &TextExpectedValue) -> anyhow::Result<()> {
    match expected.r#type.as_ref() {
        Some(text_expected_value::Type::Skipped(_)) => Ok(()),
        Some(text_expected_value::Type::Regex(regex)) => {
            verify_regex(actual, &regex.value).context("regex from endorsement does not match")
        }
        Some(text_expected_value::Type::StringLiterals(string_literals)) => {
            if string_literals.value.iter().any(|sl| sl == actual) {
                Ok(())
            } else {
                Err(anyhow::anyhow!(format!(
                    "value doesn't match the reference value string literal: {actual}"
                )))
            }
        }
        None => Err(anyhow::anyhow!("missing skip or value in the text expected value")),
    }
}

#[cfg(feature = "regex")]
fn verify_regex(actual: &str, regex: &str) -> anyhow::Result<()> {
    let re = Regex::new(regex)
        .map_err(|msg| anyhow::anyhow!("couldn't parse regex in the reference value: {msg}"))?;
    Ok(anyhow::ensure!(
        re.is_match(actual),
        format!("value doesn't match the reference value regex: {actual}")
    ))
}

#[cfg(not(feature = "regex"))]
fn verify_regex(_actual: &str, _regex: &str) -> anyhow::Result<()> {
    Err(anyhow::anyhow!("verification of regex values not supported"))
}
