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
use oak_proto_rust::oak::{
    attestation::v1::{
        AmdAttestationReport, AmdSevExpectedValues, InsecureExpectedValues,
        IntelTdxAttestationReport, IntelTdxExpectedValues, RootLayerEvidence, TcbVersion,
        TeePlatform,
    },
    RawDigest,
};
use oak_sev_snp_attestation_report::AttestationReport;
use x509_cert::{
    der::{Decode, DecodePem},
    Certificate,
};
use zerocopy::FromBytes;

use crate::{
    amd::{
        get_product_name, verify_attestation_report_signature, verify_cert_signature, ProductName,
    },
    util::hash_sha2_256,
};

const ASK_MILAN_CERT_PEM: &str = include_str!("../data/ask_milan.pem");
const ASK_GENOA_CERT_PEM: &str = include_str!("../data/ask_genoa.pem");
const ASK_TURIN_CERT_PEM: &str = include_str!("../data/ask_turin.pem");

/// Verifies the signature chain for the attestation report included in the
/// root.
pub fn verify_root_attestation_signature(
    _now_utc_millis: i64,
    root_layer: &RootLayerEvidence,
    serialized_certificate: &[u8],
) -> anyhow::Result<()> {
    match root_layer.platform() {
        TeePlatform::Unspecified => anyhow::bail!("unspecified TEE platform"),
        TeePlatform::AmdSevSnp => {
            let attestation_report = AttestationReport::ref_from_bytes(
                &root_layer.remote_attestation_report,
            )
            .map_err(|err| anyhow::anyhow!("invalid AMD SEV-SNP attestation report: {}", err))?;

            // Ensure the Attestation report is properly signed by the platform and the
            // corresponding certificate is signed by AMD.
            verify_amd_sev_snp_attestation_report_validity(
                attestation_report,
                serialized_certificate,
                _now_utc_millis,
            )
            .context("couldn't verify AMD SEV-SNP attestation report validity")?;

            // Check that the root ECA public key for the DICE chain is bound to the
            // attestation report to ensure that the entire chain is valid.
            let expected = &hash_sha2_256(&root_layer.eca_public_key[..])[..];
            let actual = attestation_report.data.report_data;

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

pub(crate) fn verify_amd_sev_snp_attestation_report_validity(
    attestation_report: &AttestationReport,
    serialized_certificate: &[u8],
    _milliseconds_since_epoch: i64,
) -> anyhow::Result<()> {
    // We demand that product-specific ASK signs the VCEK.
    let vcek = Certificate::from_der(serialized_certificate)
        .map_err(|err| anyhow::anyhow!("couldn't parse VCEK certificate: {:?}", err))?;

    let product_name = get_product_name(&vcek)?;
    let ask_cert_pem = match product_name {
        ProductName::Invalid => anyhow::bail!("unsupported AMD product"),
        ProductName::Milan => ASK_MILAN_CERT_PEM,
        ProductName::Genoa => ASK_GENOA_CERT_PEM,
        ProductName::Turin => ASK_TURIN_CERT_PEM,
    };
    let ask = Certificate::from_pem(ask_cert_pem)
        .map_err(|_err| anyhow::anyhow!("couldn't parse ASK certificate for {:?}", product_name))?;

    // TODO(#4747): user current date as part of VCEK verification.
    verify_cert_signature(&ask, &vcek).context("couldn't verify VCEK certificate")?;

    // Validate attestation report signature format.
    attestation_report.validate().map_err(|msg| anyhow::anyhow!(msg))?;

    // Ensure that the attestation report is signed by the VCEK public key.
    verify_attestation_report_signature(&vcek, attestation_report)
        .context("couldn't verify attestation report signature")?;

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
    let hardware_id = report.data.chip_id.as_ref().to_vec();
    let initial_measurement = report.data.measurement.as_ref().to_vec();
    let report_data = report.data.report_data.as_ref().to_vec();
    let vmpl = report.data.vmpl;

    Ok(AmdAttestationReport {
        current_tcb,
        reported_tcb,
        debug,
        initial_measurement,
        hardware_id,
        report_data,
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
