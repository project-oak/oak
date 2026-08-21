//
// Copyright 2025 The Project Oak Authors
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

//! Utilities for validating Intel provisioning certificates and attestation
//! quotes.

use core::convert::Into;

use anyhow::{Context, anyhow};
use const_oid::AssociatedOid;
use oak_digest::{Sha256, Sha384};
use oak_tdx_quote::{EnclaveReportBody, QeCertificationData, TdxQuoteWrapper};
use oak_time::Instant;
use p256::{
    EncodedPoint,
    ecdsa::{Signature, VerifyingKey, signature::Verifier},
};
use x509_cert::{
    Certificate,
    der::{Decode, DecodePem, referenced::OwnedToRef},
    ext::pkix::{BasicConstraints, KeyUsage},
};

use crate::x509::{check_certificate_validity, verify_cert_signature};

const PCK_ROOT: &str = include_str!("../data/Intel_SGX_Provisioning_Certification_RootCA.pem");
/// The size in bytes of a SHA2-384 digest.
const SHA2_384_DIGEST_SIZE: usize = 48;

// Identity of the Intel TDX Quoting Enclave (TD_QE), as published by Intel at
// <https://api.trustedservices.intel.com/tdx/certification/v4/qe/identity>.
//
// The PCK only certifies that the QE report was produced by some enclave
// running on a genuine Intel platform, so the report must also be checked
// against this identity before the attestation key it carries is trusted.

/// The measurement of the key used to sign the Intel TD_QE.
const TD_QE_MR_SIGNER: [u8; 32] = [
    0xdc, 0x9e, 0x2a, 0x7c, 0x6f, 0x94, 0x8f, 0x17, 0x47, 0x4e, 0x34, 0xa7, 0xfc, 0x43, 0xed, 0x03,
    0x0f, 0x7c, 0x15, 0x63, 0xf1, 0xba, 0xbd, 0xdf, 0x63, 0x40, 0xc8, 0x2e, 0x0e, 0x54, 0xa8, 0xc5,
];
/// The product ID of the Intel TD_QE.
const TD_QE_ISV_PROD_ID: u16 = 2;
/// The expected `MISCSELECT` of the Intel TD_QE, after applying the mask.
const TD_QE_MISC_SELECT: u32 = 0x0000_0000;
/// The mask applied to `MISCSELECT` before comparing it to the expected value.
const TD_QE_MISC_SELECT_MASK: u32 = 0xffff_ffff;
/// The expected `ATTRIBUTES` of the Intel TD_QE, after applying the mask.
const TD_QE_ATTRIBUTES: [u8; 16] = [
    0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
];
/// The mask applied to `ATTRIBUTES` before comparing it to the expected value.
const TD_QE_ATTRIBUTES_MASK: [u8; 16] = [
    0xfb, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
];

/// Verifies that the TDX Attestation Quote is correctly signed and that the
/// entire chain of trust is valid all the way to the Provisioning Certification
/// Key (PCK) root certificate.
#[allow(unused)]
pub fn verify_intel_tdx_quote_validity(
    verification_time: Instant,
    quote: &TdxQuoteWrapper,
) -> anyhow::Result<()> {
    let signature_data = quote.parse_signature_data().context("parsing signature data")?;

    let report_certification = match signature_data.certification_data {
        QeCertificationData::QeReportCertificationData(report_certification) => {
            Ok(report_certification)
        }
        _ => Err(anyhow!("signature data contains the wrong type of certification data")),
    }?;

    // Verify that the PCK certificate chain is valid.
    let pck_leaf = verify_quote_cert_chain_and_extract_leaf(
        verification_time,
        &report_certification.certification_data,
    )
    .context("verifying quote cert chain")?;

    // Verify that the Quoting Enclave report is signed using the PCK leaf
    // certificate.
    let pck_verifying_key: VerifyingKey = pck_leaf
        .tbs_certificate
        .subject_public_key_info
        .owned_to_ref()
        .try_into()
        .map_err(|_err| anyhow::anyhow!("could not extract ECDSA P-384 public key"))?;

    let qe_signature = Signature::from_bytes(report_certification.signature.into())
        .map_err(|_err| anyhow::anyhow!("couldn't parse QE Report signature"))?;
    pck_verifying_key
        .verify(report_certification.report_body, &qe_signature)
        .map_err(|_err| anyhow::anyhow!("QE Report signature verification failed"))?;

    // Verify that the report was produced by the Intel Quoting Enclave.
    let qe_report =
        report_certification.parse_enclave_report_body().context("parsing enclave report body")?;
    verify_qe_report_identity(&qe_report).context("verifying quoting enclave identity")?;

    // Verify that the Attestation Key is bound to the Quoting Enclave Report.
    let mut key_binding_data = signature_data.ecdsa_attestation_key.to_vec();
    key_binding_data.extend_from_slice(report_certification.authentication_data);
    anyhow::ensure!(
        Sha256::from_contents(key_binding_data.as_slice()).as_ref() == &qe_report.report_data[..32],
        "attestation key is not bound to quoting enclave report"
    );
    anyhow::ensure!(
        [0u8; 32] == qe_report.report_data[32..],
        "unexpected data in quoting enclave report data"
    );

    // Verify that the Quote data is signed using the Attestation Key.
    let attestation_key = VerifyingKey::from_encoded_point(&EncodedPoint::from_untagged_bytes(
        signature_data.ecdsa_attestation_key.into(),
    ))
    .map_err(|_err| anyhow::anyhow!("couldn't parse attestation public key"))?;
    let quote_signature = Signature::from_bytes(signature_data.quote_signature.into())
        .map_err(|_err| anyhow::anyhow!("couldn't parse quote signature"))?;
    attestation_key
        .verify(quote.get_quote_data_bytes()?, &quote_signature)
        .map_err(|_err| anyhow::anyhow!("quote signature verification failed"))?;

    Ok(())
}

/// Verifies that the Quoting Enclave report identifies the Intel TD_QE.
///
/// The PCK signature over the report only proves that it was generated by an
/// enclave on a genuine Intel platform. Any enclave with the `PROVISION_KEY`
/// attribute can have its report signed by the PCE, so without this check the
/// attestation key bound to the report could belong to an arbitrary enclave.
fn verify_qe_report_identity(qe_report: &EnclaveReportBody) -> anyhow::Result<()> {
    anyhow::ensure!(
        qe_report.mr_signer == &TD_QE_MR_SIGNER,
        "quoting enclave report has unexpected MRSIGNER"
    );
    anyhow::ensure!(
        qe_report.isv_prod_id == TD_QE_ISV_PROD_ID,
        "quoting enclave report has unexpected ISVPRODID"
    );
    anyhow::ensure!(
        qe_report.misc_select & TD_QE_MISC_SELECT_MASK == TD_QE_MISC_SELECT,
        "quoting enclave report has unexpected MISCSELECT"
    );
    let masked_attributes: [u8; 16] =
        core::array::from_fn(|i| qe_report.attributes[i] & TD_QE_ATTRIBUTES_MASK[i]);
    anyhow::ensure!(
        masked_attributes == TD_QE_ATTRIBUTES,
        "quoting enclave report has unexpected ATTRIBUTES"
    );
    Ok(())
}

pub fn verify_quote_cert_chain_and_extract_leaf(
    verification_time: Instant,
    certification_data: &QeCertificationData,
) -> anyhow::Result<Certificate> {
    let mut certificates = if let &QeCertificationData::PckCertChain(chain) = certification_data {
        Ok(Certificate::load_pem_chain(chain)
            .map_err(anyhow::Error::msg)
            .context("parsing certificate chain")?)
    } else {
        Err(anyhow!("certification data is not a PCK certificate chain"))
    }?;
    // The PCK certificate chain includes the root certificate, but we want to make
    // sure it matches the actual root certificate that was published. So we replace
    // the provided root certificate with the actual published one.
    certificates.pop().ok_or_else(|| anyhow!("certificate chain is empty"))?;
    let root = Certificate::from_pem(PCK_ROOT.as_bytes())
        .map_err(anyhow::Error::msg)
        .context("parsing known root certificate")?;
    certificates.push(root);
    let mut chain = certificates.iter();
    let mut signee = chain.next().ok_or_else(|| anyhow!("certificate chain is empty"))?;
    let leaf = signee.clone();
    // Make sure the leaf certificate is valid.
    check_certificate_validity(verification_time, &leaf)?;
    // Each certificate must be signed by the next one in the chain and the signer
    // must be valid.
    for (intermediate_count, signer) in chain.enumerate() {
        check_certificate_validity(verification_time, signer)?;
        anyhow::ensure!(
            signee.tbs_certificate.issuer == signer.tbs_certificate.subject,
            "certificate issuer does not match signer subject"
        );
        let basic_constraints = get_extension::<BasicConstraints>(signer)?
            .ok_or_else(|| anyhow!("signer certificate is missing basic constraints"))?;
        anyhow::ensure!(basic_constraints.ca, "signer certificate is not a CA");
        if let Some(path_len) = basic_constraints.path_len_constraint {
            anyhow::ensure!(
                intermediate_count <= path_len as usize,
                "certificate path length constraint exceeded"
            );
        }
        if let Some(key_usage) = get_extension::<KeyUsage>(signer)? {
            anyhow::ensure!(
                key_usage.key_cert_sign(),
                "signer certificate key usage does not permit certificate signing"
            );
        }
        verify_cert_signature(signer, signee).context("verifying cert signature")?;
        signee = signer;
    }
    Ok(leaf)
}

fn get_extension<'a, T: AssociatedOid + Decode<'a>>(
    cert: &'a Certificate,
) -> anyhow::Result<Option<T>> {
    let Some(extensions) = &cert.tbs_certificate.extensions else {
        return Ok(None);
    };
    for ext in extensions {
        if ext.extn_id == T::OID {
            return Ok(Some(
                T::from_der(ext.extn_value.as_bytes())
                    .map_err(anyhow::Error::msg)
                    .context("parsing certificate extension")?,
            ));
        }
    }
    Ok(None)
}

/// Software implementation of the RTMR logic that can be used to replay a
/// sequence of `extend` operations.
#[allow(unused)]
pub struct RtmrEmulator {
    state: [u8; SHA2_384_DIGEST_SIZE],
}

#[allow(unused)]
impl RtmrEmulator {
    pub const fn new() -> Self {
        // The initial state of an RTMR is all 0.
        Self { state: [0u8; SHA2_384_DIGEST_SIZE] }
    }

    /// Extends the RTMR with the new SHA2-384 digest.
    pub fn extend(&mut self, digest: &[u8; SHA2_384_DIGEST_SIZE]) {
        let mut current = self.state.to_vec();
        // Extension is done by concatenating the current state and the new digest, and
        // then calculating the SHA2-384 digest of that value. See section 5.4.6 of the
        // [Intel® TDX Module v1.5 ABI Specification](https://cdrdv2.intel.com/v1/dl/getContent/817877?fileName=intel-tdx-module-1.5-abi-spec-348551004.pdf)
        // for more information.
        current.extend_from_slice(digest.as_slice());
        self.state = Sha384::from_contents(&current).into();
    }

    /// Gets the current value of the RTMR.
    pub fn get_state(&self) -> &[u8] {
        &self.state
    }
}

impl Default for RtmrEmulator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
