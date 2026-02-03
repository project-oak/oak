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

//! Contains code related to AMD hardware certificates and attestation report.

use alloc::string::String;

use const_oid::ObjectIdentifier;
use oak_sev_snp_attestation_report::{AmdProduct, AttestationReport, SigningAlgorithm, TcbVersion};
use p384::ecdsa::{VerifyingKey, signature::Verifier};
use x509_cert::{Certificate, der::referenced::OwnedToRef};
use zerocopy::IntoBytes;

// The keys in the key-value map of X509 certificates are Object Identifiers
// (OIDs) which have a global registry. The present OIDs are taken from
// Table 8 of
// https://www.amd.com/content/dam/amd/en/documents/epyc-technical-docs/specifications/57230.pdf
const PRODUCT_NAME_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.2");
const BL_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.3.1");
const TEE_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.3.2");
const SNP_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.3.3");
const CHIP_ID_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.4");
const UCODE_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.3.8");
const FMC_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.3.9");

/// Extracts the product name from the VCEK certificate.
pub fn get_product(cert: &Certificate) -> anyhow::Result<AmdProduct> {
    let exts = cert
        .tbs_certificate
        .extensions
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("could not get extensions from cert"))?;
    let pn_ext = exts
        .iter()
        .find(|&ext| ext.extn_id == PRODUCT_NAME_OID)
        .ok_or_else(|| anyhow::anyhow!("no product name found in cert"))?;
    let raw = String::from_utf8(pn_ext.extn_value.as_bytes().to_vec())
        .map_err(|_utf8_err| anyhow::anyhow!("failed to read product name"))?;
    if raw.contains("Turin") {
        Ok(AmdProduct::Turin)
    } else if raw.contains("Genoa") {
        Ok(AmdProduct::Genoa)
    } else if raw.contains("Milan") {
        Ok(AmdProduct::Milan)
    } else {
        Ok(AmdProduct::Unsupported)
    }
}

fn chip_id(cert: &Certificate) -> anyhow::Result<[u8; 64]> {
    let exts = cert
        .tbs_certificate
        .extensions
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("could not get extensions from cert"))?;
    let chip_id_ext = exts
        .iter()
        .find(|&ext| ext.extn_id == CHIP_ID_OID)
        .ok_or_else(|| anyhow::anyhow!("no chip ID found in cert"))?;
    let chip_id = chip_id_ext.extn_value.as_bytes().to_vec();
    // From Turin (and later) AMD reduced the length of the Chip ID from 64 to
    // 8 bytes. We need to be prepared for both cases. See Note 4 in
    // Section 3.1. of
    // https://www.amd.com/content/dam/amd/en/documents/epyc-technical-docs/specifications/57230.pdf
    anyhow::ensure!(
        chip_id.len() == 8 || chip_id.len() == 64,
        "unexpected length of chip ID value"
    );

    // Copy into array of fixed length.
    let mut result = [0; 64];
    result[0..chip_id.len()].copy_from_slice(&chip_id);
    Ok(result)
}

/// Parses the TCB version contained in the VCEK certificate.
fn parse_tcb_version(vcek: &Certificate) -> anyhow::Result<TcbVersion> {
    let mut tcb = TcbVersion { ..Default::default() };
    for ext in vcek
        .tbs_certificate
        .extensions
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("could not get extensions from VCEK cert"))?
    {
        // What's the appropriate way of extracting u8 from OctetString?
        let arr = ext.extn_value.as_bytes();
        let last = arr.len() - 1;
        if ext.extn_id == BL_OID {
            tcb.boot_loader = arr[last];
        } else if ext.extn_id == TEE_OID {
            tcb.tee = arr[last];
        } else if ext.extn_id == SNP_OID {
            tcb.snp = arr[last];
        } else if ext.extn_id == UCODE_OID {
            tcb.microcode = arr[last];
        } else if ext.extn_id == FMC_OID {
            tcb.fmc = arr[last];
        }
    }
    Ok(tcb)
}

pub fn verify_attestation_report_signature(
    vcek: &Certificate,
    report: &AttestationReport,
) -> anyhow::Result<()> {
    // First check some necessary conditions for the signature to be valid.
    let arpt_chip_id = report.data.chip_id;
    let vcek_chip_id = chip_id(vcek)?;
    anyhow::ensure!(
        arpt_chip_id == vcek_chip_id,
        "chip id differs: reported={} vcek={}",
        hex::encode(arpt_chip_id),
        hex::encode(vcek_chip_id)
    );

    let reported_tcb = report.data.get_reported_tcb_version();
    let vcek_tcb = parse_tcb_version(vcek)?;
    anyhow::ensure!(
        reported_tcb == vcek_tcb,
        "mismatch in TCB version: reported={:?} vcek={:?}",
        reported_tcb,
        vcek_tcb
    );
    anyhow::ensure!(
        report.data.get_signature_algo() == Some(SigningAlgorithm::EcdsaP384Sha384),
        "invalid signature algoritm: {:?}",
        report.data.get_signature_algo(),
    );

    let verifying_key: VerifyingKey = vcek
        .tbs_certificate
        .subject_public_key_info
        .owned_to_ref()
        .try_into()
        .map_err(|_err| anyhow::anyhow!("could not extract ECDSA P-384 public key"))?;

    let message = report.data.as_bytes();

    // `report.signature.{r,s}` contain 48 bytes, the rest is zero padded
    // to allow longer signatures as well. The 48 bytes are interpreted as
    // a single little-endian encoded integer. `p384::ecdsa::Signature`
    // requires big-endian, so need to mirror.
    let mut r: [u8; 48] = [0; 48];
    let mut s: [u8; 48] = [0; 48];
    for i in 0..48 {
        let j = 47 - i;
        r[i] = report.signature.r[j];
        s[i] = report.signature.s[j];
    }
    let signature = p384::ecdsa::Signature::from_scalars(r, s)
        .map_err(|_err| anyhow::anyhow!("could not extract ECDSA P-384 signature"))?;

    verifying_key
        .verify(message, &signature)
        .map_err(|_err| anyhow::anyhow!("failed to verify ECDSA P-384 signature"))
}

#[cfg(test)]
mod tests;
