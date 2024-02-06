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

use oak_sev_snp_attestation_report::{AttestationReport, SigningAlgorithm, TcbVersion};
use p256::pkcs8::ObjectIdentifier;
use rsa::{pss::Signature, signature::Verifier, RsaPublicKey};
use sha2::Sha384;
use x509_cert::{
    der::{referenced::OwnedToRef, Encode},
    Certificate, Version,
};
use zerocopy::{AsBytes, FromZeroes};

// The keys in the key-value map of X509 certificates are Object Identifiers
// (OIDs) which have a global registry. The present OIDs are taken from
// Table 8 of
// https://www.amd.com/content/dam/amd/en/documents/epyc-technical-docs/specifications/57230.pdf
const RSA_SSA_PSS_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.2.840.113549.1.1.10");
const _PRODUCT_NAME_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.2");
const BL_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.3.1");
const TEE_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.3.2");
const SNP_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.3.3");
const CHIP_ID_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.4");
const UCODE_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.3.8");

// Verifies validity of a matching ARK, ASK certificate pair.
//
// Validate at least a subset of Appendix B.3 of
// https://www.amd.com/content/dam/amd/en/documents/epyc-technical-docs/programmer-references/55766_SEV-KM_API_Specification.pdf
// Ideally, we'd check everything listed there.
pub fn validate_ark_ask_certs(ark: &Certificate, ask: &Certificate) -> anyhow::Result<()> {
    anyhow::ensure!(
        ark.tbs_certificate.version == Version::V3,
        "unexpected version of ARK cert"
    );
    anyhow::ensure!(
        ask.tbs_certificate.version == Version::V3,
        "unexpected version of ASK cert"
    );

    verify_cert_signature(ark, ask)?;
    verify_cert_signature(ark, ark)?;

    Ok(())
}

pub fn verify_cert_signature(signer: &Certificate, signee: &Certificate) -> anyhow::Result<()> {
    anyhow::ensure!(
        signee.signature_algorithm.oid == RSA_SSA_PSS_OID,
        "unsupported signature algorithm: {:?}",
        signee.signature_algorithm
    );

    let verifying_key = {
        let pubkey_info = signer
            .tbs_certificate
            .subject_public_key_info
            .owned_to_ref();
        let pubkey = RsaPublicKey::try_from(pubkey_info)
            .map_err(|_err| anyhow::anyhow!("could not parse RSA public key"))?;
        rsa::pss::VerifyingKey::<Sha384>::new(pubkey)
    };

    let message = signee
        .tbs_certificate
        .to_der()
        .map_err(|_err| anyhow::anyhow!("could not extract message to verify RSA signature"))?;
    let signature = Signature::try_from(signee.signature.raw_bytes())
        .map_err(|_err| anyhow::anyhow!("could not extract RSA signature"))?;

    verifying_key
        .verify(&message, &signature)
        .map_err(|_err| anyhow::anyhow!("signature verification failed"))
}

// Currently unused, use `pub` only to disable the warning.
fn _product_name(cert: &Certificate) -> anyhow::Result<String> {
    let exts = cert
        .tbs_certificate
        .extensions
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("could not get extensions from cert"))?;
    let pn_ext = exts
        .iter()
        .find(|&ext| ext.extn_id == _PRODUCT_NAME_OID)
        .ok_or_else(|| anyhow::anyhow!("no product name found in cert"))?;
    String::from_utf8(pn_ext.extn_value.as_bytes().to_vec())
        .map_err(|_utf8_err| anyhow::anyhow!("failed to read product name"))
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
    anyhow::ensure!(chip_id.len() == 64, "length of chip ID value is not 64");

    // Copy into array of fixed length.
    let mut result = [0; 64];
    result.copy_from_slice(&chip_id[0..64]);
    Ok(result)
}

fn tcb_version(vcek: &Certificate) -> anyhow::Result<TcbVersion> {
    let mut tcb = TcbVersion::new_zeroed();
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
        "chip id differs attestation={} vcek={}",
        hex::encode(arpt_chip_id),
        hex::encode(vcek_chip_id)
    );

    let arpt_tcb = &report.data.reported_tcb;
    let vcek_tcb = tcb_version(vcek)?;
    anyhow::ensure!(
        arpt_tcb.snp == vcek_tcb.snp,
        "mismatch in snp field of TCB version: report={} vcek={}",
        arpt_tcb.snp,
        vcek_tcb.snp
    );
    anyhow::ensure!(
        arpt_tcb.microcode == vcek_tcb.microcode,
        "mismatch in microcode field of TCB version: report={} vcek={}",
        arpt_tcb.microcode,
        vcek_tcb.microcode
    );
    anyhow::ensure!(
        arpt_tcb.tee == vcek_tcb.tee,
        "mismatch in tee field of TCB version: report={} vcek={}",
        arpt_tcb.tee,
        vcek_tcb.tee
    );
    anyhow::ensure!(
        arpt_tcb.boot_loader == vcek_tcb.boot_loader,
        "mismatch in boot_loader field of TCB version: report={} vcek={}",
        arpt_tcb.boot_loader,
        vcek_tcb.boot_loader
    );
    anyhow::ensure!(
        report.data.get_signature_algo() == Some(SigningAlgorithm::EcdsaP384Sha384),
        "invalid signature algoritm: {:?}",
        report.data.get_signature_algo(),
    );

    let verifying_key = {
        let pubkey_info = vcek.tbs_certificate.subject_public_key_info.owned_to_ref();
        p384::ecdsa::VerifyingKey::from_sec1_bytes(pubkey_info.subject_public_key.raw_bytes())
            .map_err(|_err| anyhow::anyhow!("could not extract ECDSA P-384 public key"))
    }?;
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
