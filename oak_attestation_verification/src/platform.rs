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
use digest_util::hash_sha2_256;
use oak_proto_rust::oak::{
    attestation::v1::{
        tcb_version_expected_value, AmdAttestationReport, AmdSevExpectedValues,
        InsecureExpectedValues, IntelTdxAttestationReport, IntelTdxExpectedValues,
        RootLayerEvidence, TcbVersion, TeePlatform,
    },
    RawDigest,
};
use oak_sev_snp_attestation_report::{AmdProduct, AttestationReport};
use oak_time::Instant;
use x509_cert::{
    der::{Decode, DecodePem},
    Certificate,
};
use zerocopy::FromBytes;

use crate::{
    amd::{get_product, verify_attestation_report_signature},
    x509::{check_certificate_validity, verify_cert_signature},
};

const ASK_MILAN_CERT_PEM: &str = include_str!("../data/ask_milan.pem");
const ASK_GENOA_CERT_PEM: &str = include_str!("../data/ask_genoa.pem");
const ASK_TURIN_CERT_PEM: &str = include_str!("../data/ask_turin.pem");

/// Check that the root ECA public key for the DICE chain is bound to the
/// attestation report to ensure that the entire chain is valid.
pub fn verify_dice_root_eca_key(
    attestation_report: &AttestationReport,
    eca_public_key: &[u8],
) -> anyhow::Result<()> {
    let expected = &hash_sha2_256(eca_public_key)[..];
    let actual = attestation_report.data.report_data;
    anyhow::ensure!(
        // The report data contains 64 bytes by default, but we only use the
        // first 32 bytes at the moment.
        expected.len() < actual.len() && expected == &actual[..expected.len()],
        "the root ECA public key is not bound to the AMD SEV-SNP attestation report"
    );
    Ok(())
}

/// Verifies the signature chain for the attestation report included in the
/// root.
pub fn verify_root_attestation_signature(
    current_time: Instant,
    check_cert_expiry: bool,
    root_layer: &RootLayerEvidence,
    tee_certificate: &[u8],
) -> anyhow::Result<()> {
    match root_layer.platform() {
        TeePlatform::Unspecified => anyhow::bail!("unspecified TEE platform"),
        TeePlatform::AmdSevSnp => {
            let attestation_report = AttestationReport::ref_from_bytes(
                &root_layer.remote_attestation_report,
            )
            .map_err(|err| anyhow::anyhow!("invalid AMD SEV-SNP attestation report: {}", err))?;

            let vcek_cert = Certificate::from_der(tee_certificate)
                .map_err(|err| anyhow::anyhow!("couldn't parse VCEK certificate: {:?}", err))?;

            // Ensure the Attestation report is properly signed by the platform and the
            // corresponding certificate is signed by AMD.
            verify_amd_sev_snp_attestation_report_validity(
                current_time,
                check_cert_expiry,
                attestation_report,
                &vcek_cert,
            )
            .context("verifying AMD SEV-SNP attestation report validity")?;
            verify_dice_root_eca_key(attestation_report, &root_layer.eca_public_key)
        }
        TeePlatform::IntelTdx => anyhow::bail!("not supported"),

        // For non-AMD-SEV-SNP and non-Intel-TDX we just verify that the
        // attestation report contains the expected public key.
        TeePlatform::None => {
            let attestation_report = AttestationReport::ref_from_bytes(
                &root_layer.remote_attestation_report,
            )
            .map_err(|err| anyhow::anyhow!("failed to parse attestation report: {}", err))?;
            verify_dice_root_eca_key(attestation_report, &root_layer.eca_public_key)
        }
    }
}

pub(crate) fn verify_amd_sev_snp_attestation_report_validity(
    current_time: Instant,
    check_cert_expiry: bool,
    attestation_report: &AttestationReport,
    vcek_cert: &Certificate,
) -> anyhow::Result<()> {
    let product = get_product(vcek_cert)?;
    let ask_cert_pem = match product {
        AmdProduct::Unsupported => anyhow::bail!("unsupported AMD product"),
        AmdProduct::Milan => ASK_MILAN_CERT_PEM,
        AmdProduct::Genoa => ASK_GENOA_CERT_PEM,
        AmdProduct::Turin => ASK_TURIN_CERT_PEM,
    };
    let ask = Certificate::from_pem(ask_cert_pem)
        .map_err(|_err| anyhow::anyhow!("couldn't parse ASK certificate for {:?}", product))?;

    if check_cert_expiry {
        check_certificate_validity(current_time, vcek_cert)
            .context("checking VCEK cert validity")?;
    }

    // We demand that the product-specific ASK signs the VCEK.
    verify_cert_signature(&ask, vcek_cert).context("verifying VCEK cert signature")?;

    // Validate attestation report signature format.
    attestation_report.validate().map_err(|msg| anyhow::anyhow!(msg))?;

    // Ensure that the attestation report is signed by the VCEK public key.
    verify_attestation_report_signature(vcek_cert, attestation_report)
        .context("verifying attestation report signature")
}

// Returns Ok whenever each component in `expected` is less or equal to the
// corresponding component in `actual`.
fn is_less_or_equal(expected: &TcbVersion, actual: &TcbVersion) -> anyhow::Result<()> {
    anyhow::ensure!(
        expected.boot_loader <= actual.boot_loader,
        format!("unsupported boot loader version: {}", actual.boot_loader)
    );
    anyhow::ensure!(expected.tee <= actual.tee, format!("unsupported tee version: {}", actual.tee));
    anyhow::ensure!(expected.snp <= actual.snp, format!("unsupported snp version: {}", actual.snp));
    anyhow::ensure!(
        expected.microcode <= actual.microcode,
        format!("unsupported microcode version: {}", actual.microcode)
    );
    anyhow::ensure!(expected.fmc <= actual.fmc, format!("unsupported FMC version: {}", actual.fmc));
    Ok(())
}

/// Verifies the AMD SEV attestation report flag values.
pub fn verify_amd_sev_attestation_report_values(
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

    // Legacy TCB version comparison (deprecated).
    // TODO: b/433225656 - Remove this block.
    #[allow(deprecated)]
    match (
        expected_values.min_tcb_version.as_ref(),
        attestation_report_values.reported_tcb.as_ref(),
    ) {
        (Some(min_tcb_version), Some(reported_tcb_version)) => {
            return is_less_or_equal(min_tcb_version, reported_tcb_version);
        }
        (Some(_), None) => anyhow::bail!("no reported TCB version in the attestation report"),
        // No legacy reference values - fall through to next block.
        (None, _) => {}
    }

    // Compare required and reported TCB versions.
    let per_product_rv = match attestation_report_values.product {
        0 => anyhow::bail!("unsupported AMD product"),
        1 => expected_values.milan.context("no TCB version reference value for AMD Milan")?,
        2 => expected_values.genoa.context("no TCB version reference value for AMD Genoa")?,
        3 => expected_values.turin.context("no TCB version reference value for AMD Turin")?,
        _ => anyhow::bail!("invalid enum value"),
    };
    match (per_product_rv.r#type, attestation_report_values.reported_tcb.as_ref()) {
        (Some(tcb_version_expected_value::Type::Skipped(_)), _) => Ok(()),
        (
            Some(tcb_version_expected_value::Type::Minimum(min_tcb_version)),
            Some(reported_tcb_version),
        ) => is_less_or_equal(&min_tcb_version, reported_tcb_version),
        (Some(tcb_version_expected_value::Type::Minimum(_)), None) => {
            anyhow::bail!("no reported TCB version")
        }
        (None, _) => anyhow::bail!("no per-model TCB version reference value"),
    }
}

fn tcb_version_struct_to_proto(
    as_struct: &oak_sev_snp_attestation_report::TcbVersion,
) -> TcbVersion {
    TcbVersion {
        boot_loader: as_struct.boot_loader.into(),
        tee: as_struct.tee.into(),
        snp: as_struct.snp.into(),
        microcode: as_struct.microcode.into(),
        fmc: as_struct.fmc.into(),
    }
}

pub fn convert_amd_sev_snp_attestation_report(
    report: &AttestationReport,
) -> anyhow::Result<AmdAttestationReport> {
    let current_tcb_struct = report.data.get_current_tcb_version();
    let reported_tcb_struct = report.data.get_reported_tcb_version();
    let current_tcb = Some(tcb_version_struct_to_proto(&current_tcb_struct));
    let reported_tcb = Some(tcb_version_struct_to_proto(&reported_tcb_struct));

    let debug = report.has_debug_flag().map_err(|error| anyhow::anyhow!(error))?;
    let product_proto_enum = match report.data.get_product() {
        AmdProduct::Unsupported => oak_proto_rust::oak::attestation::v1::AmdProduct::Unsupported,
        AmdProduct::Milan => oak_proto_rust::oak::attestation::v1::AmdProduct::Milan,
        AmdProduct::Genoa => oak_proto_rust::oak::attestation::v1::AmdProduct::Genoa,
        AmdProduct::Turin => oak_proto_rust::oak::attestation::v1::AmdProduct::Turin,
    };
    let hardware_id = report.data.chip_id.as_ref().to_vec();
    let initial_measurement = report.data.measurement.as_ref().to_vec();
    let report_data = report.data.report_data.as_ref().to_vec();
    let vmpl = report.data.vmpl;

    Ok(AmdAttestationReport {
        report_data,
        current_tcb,
        reported_tcb,
        debug,
        product: product_proto_enum.into(),
        initial_measurement,
        hardware_id,
        vmpl,
    })
}

pub fn convert_amd_sev_snp_initial_measurement(initial_measurement: &[u8]) -> RawDigest {
    RawDigest { sha2_384: initial_measurement.to_vec(), ..Default::default() }
}

/// Verifies the Intel TDX attestation report.
pub fn verify_intel_tdx_attestation_report(
    _attestation_report_values: &IntelTdxAttestationReport,
    _expected_values: &IntelTdxExpectedValues,
) -> anyhow::Result<()> {
    anyhow::bail!("needs implementation")
}

/// Verifies insecure attestation.
pub fn verify_insecure(_expected_values: &InsecureExpectedValues) -> anyhow::Result<()> {
    Ok(())
}
