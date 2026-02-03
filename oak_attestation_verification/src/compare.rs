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
use digest_util::is_raw_digest_match;
use oak_proto_rust::oak::{
    RawDigest,
    attestation::v1::{
        ApplicationLayerData, ApplicationLayerExpectedValues, CbData, CbExpectedValues,
        ContainerLayerData, ContainerLayerExpectedValues, EventData, EventExpectedValues,
        ExpectedDigests, ExpectedValues, ExtractedEvidence, KernelLayerData,
        KernelLayerExpectedValues, OakContainersData, OakContainersExpectedValues,
        OakRestrictedKernelData, OakRestrictedKernelExpectedValues, RootLayerData,
        RootLayerExpectedValues, SystemLayerData, SystemLayerExpectedValues, TextExpectedValue,
        expected_digests, expected_values, extracted_evidence::EvidenceValues,
        root_layer_data::Report, text_expected_value,
    },
};
#[cfg(feature = "regex")]
use regex_lite::Regex;

use crate::platform::{
    convert_amd_sev_snp_initial_measurement, verify_amd_sev_attestation_report_values,
    verify_insecure, verify_intel_tdx_attestation_quote,
};

pub fn compare_expected_values(
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
        #[allow(deprecated)]
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
    // Compare root layer
    if let (Some(values_root), Some(expected_root)) = (&values.root_layer, &expected.root_layer) {
        compare_root_layer_measurement_digests(values_root, expected_root)
            .context("root layer verification failed")?;
    } else if values.root_layer.is_some() || expected.root_layer.is_some() {
        return Err(anyhow::anyhow!("root layer mismatch"));
    }

    // Compare layers vector
    if values.layers.len() != expected.layers.len() {
        return Err(anyhow::anyhow!(
            "Number of layers doesn't match: {} {}",
            values.layers.len(),
            expected.layers.len()
        ));
    }
    for (value_layer, expected_layer) in values.layers.iter().zip(expected.layers.iter()) {
        compare_event_measurement_digests(value_layer, expected_layer)
            .context("layer verification failed")?;
    }

    Ok(())
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
            compare_firmware_layer_measurement_digests(
                &report_values.initial_measurement,
                amd_sev_values
                    .stage0_expected
                    .as_ref()
                    .context("no stage0 expected value provided")?,
            )
            .context("comparing firmware layer digests")?;
            verify_amd_sev_attestation_report_values(report_values, amd_sev_values)
        }
        (Some(Report::Tdx(quote_values)), _, Some(intel_tdx_values), _) => {
            verify_intel_tdx_attestation_quote(quote_values, intel_tdx_values)
        }
        (_, _, _, Some(insecure_values)) => {
            verify_insecure(insecure_values).context("verifying insecure")
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

pub(crate) fn compare_firmware_layer_measurement_digests(
    initial_measurement: &[u8],
    expected_values: &ExpectedDigests,
) -> anyhow::Result<()> {
    let measurement = convert_amd_sev_snp_initial_measurement(initial_measurement);
    compare_measurement_digest(&measurement, expected_values)
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
    .context("comparing kernel image digests")?;

    compare_measurement_digest(
        values.kernel_setup_data.as_ref().context("no kernel setup data evidence value")?,
        expected_kernel_values
            .setup_data
            .as_ref()
            .context("expected values contained no setup_data digests")?,
    )
    .context("comparing kernel setup data digests")?;

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
    .context("comparing init_ram_fs digests")?;
    compare_measurement_digest(
        values.memory_map.as_ref().context("no memory_map value provided")?,
        expected.memory_map.as_ref().context("no memory_map expected value provided")?,
    )
    .context("comparing memory_map digests")?;
    compare_measurement_digest(
        values.acpi.as_ref().context("no ACPI table value provided")?,
        expected.acpi.as_ref().context("no ACPI table expected value provided")?,
    )
    .context("comparing ACPI digests")
}

pub(crate) fn compare_event_measurement_digests(
    values: &EventData,
    expected: &EventExpectedValues,
) -> anyhow::Result<()> {
    compare_measurement_digest(
        values.event.as_ref().context("no event evidence value")?,
        expected.event.as_ref().context("no event image value")?,
    )
}

pub(crate) fn compare_system_layer_measurement_digests(
    values: &SystemLayerData,
    expected: &SystemLayerExpectedValues,
) -> anyhow::Result<()> {
    compare_measurement_digest(
        values.system_image.as_ref().context("no system image evidence value")?,
        expected.system_image.as_ref().context("no expected system image value")?,
    )
}

pub(crate) fn compare_application_layer_measurement_digests(
    values: &ApplicationLayerData,
    expected: &ApplicationLayerExpectedValues,
) -> anyhow::Result<()> {
    compare_measurement_digest(
        values.binary.as_ref().context("no binary evidence value")?,
        expected.binary.as_ref().context("no expected binary value")?,
    )
    .context("comparing application binary digests")?;
    compare_measurement_digest(
        values.config.as_ref().context("no config evidence value")?,
        expected.configuration.as_ref().context("no expected config value")?,
    )
    .context("comparing application config digests")
}

pub(crate) fn compare_container_layer_measurement_digests(
    values: &ContainerLayerData,
    expected: &ContainerLayerExpectedValues,
) -> anyhow::Result<()> {
    compare_measurement_digest(
        values.bundle.as_ref().context("no bundle evidence value")?,
        expected.bundle.as_ref().context("no expected bundle value")?,
    )
    .context("comparing container bundle digests")?;
    compare_measurement_digest(
        values.config.as_ref().context("no config evidence value")?,
        expected.config.as_ref().context("no expected config value")?,
    )
    .context("comparing container config digests")
}

/// Verifies the measurement digest value against a reference value and
/// the expected digests calculated from endorsements and reference values.
pub(crate) fn compare_measurement_digest(
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
            verify_regex(actual, &regex.value).context("verifying regex")
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
    anyhow::ensure!(
        re.is_match(actual),
        format!("value doesn't match the reference value regex: {actual}")
    );
    Ok(())
}

#[cfg(not(feature = "regex"))]
fn verify_regex(_actual: &str, _regex: &str) -> anyhow::Result<()> {
    Err(anyhow::anyhow!("verification of regex values not supported"))
}
