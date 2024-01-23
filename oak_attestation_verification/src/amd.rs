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

//! Contains structs for specifying in-toto statements and claims about

use alloc::string::String;

use oak_sev_guest::guest::{AttestationReport, TcbVersion};
use p256::pkcs8::ObjectIdentifier;
use rsa::{pss::Signature, signature::Verifier, RsaPublicKey};
use sha2::Sha384;
use x509_cert::{
    der::{referenced::OwnedToRef, Encode},
    Certificate, Version,
};
use zerocopy::{AsBytes, FromZeroes};

const RSA_SSA_PSS_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.2.840.113549.1.1.10");
const PRODUCT_NAME_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.3704.1.2");
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
    if ark.tbs_certificate.version != Version::V3 {
        anyhow::bail!("unexpected version of ARK cert");
    }

    if ask.tbs_certificate.version != Version::V3 {
        anyhow::bail!("unexpected version of ASK cert");
    }

    verify_cert_signature(ark, ask)?;
    verify_cert_signature(ark, ark)?;

    Ok(())
}

pub fn verify_cert_signature(signer: &Certificate, signee: &Certificate) -> anyhow::Result<()> {
    if signee.signature_algorithm.oid != RSA_SSA_PSS_OID {
        anyhow::bail!(
            "unsupported signature algorithm: {:?}",
            signee.signature_algorithm
        );
    }

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

    Ok(verifying_key
        .verify(&message, &signature)
        .map_err(|_err| anyhow::anyhow!("signature verification failed"))?)
}

fn to_array_64<T>(slice: &[T]) -> anyhow::Result<&[T; 64]> {
    if slice.len() == 64 {
        let ptr = slice.as_ptr() as *const [T; 64];
        unsafe { Ok(&*ptr) }
    } else {
        anyhow::bail!("unexpected length of chip ID")
    }
}

fn product_name(vcek: &Certificate) -> anyhow::Result<String> {
    for ext in vcek
        .tbs_certificate
        .extensions
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("could not get extensions from VCEK cert"))?
    {
        if ext.extn_id == PRODUCT_NAME_OID {
            return String::from_utf8(ext.extn_value.as_bytes().to_vec())
                .map_err(|_utf8_err| anyhow::anyhow!("failed to read product name"));
        }
    }
    Err(anyhow::anyhow!("no product name found in VCEK vert"))
}

fn chip_id(vcek: &Certificate) -> anyhow::Result<[u8; 64]> {
    for ext in vcek
        .tbs_certificate
        .extensions
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("could not get extensions from VCEK cert"))?
    {
        if ext.extn_id == CHIP_ID_OID {
            let chip_id = ext.extn_value.as_bytes().to_vec();
            return to_array_64(&chip_id).copied();
        }
    }
    Err(anyhow::anyhow!("no chip ID found in VCEK vert"))
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

// fn eprint_ext(cert: &Certificate) -> anyhow::Result<()> {
//     for ext in cert
//         .tbs_certificate
//         .extensions
//         .as_ref()
//         .ok_or_else(|| anyhow::anyhow!("could not get extensions from cert"))?
//     {
//         eprintln!(
//             "cert ext id={} val={}",
//             ext.extn_id,
//             hex::encode(ext.extn_value.as_bytes())
//         );
//     }
//     Ok(())
// }

pub fn verify_attestation_report_signature(
    vcek: &Certificate,
    report: &AttestationReport,
) -> anyhow::Result<()> {
    // eprint_ext(vcek)?;

    // eprintln!("VCEK product name: {}", product_name(vcek)?);
    // let rtcb = &report.data.reported_tcb;
    // let ctcb = &report.data.current_tcb;
    // let vtcb = &tcb_version(vcek)?;
    // eprintln!(
    //     "ARPT reported TCB version: ucodeSPL={}&snpSPL={}&teeSPL={}&blSPL={}",
    //     rtcb.microcode, rtcb.snp, rtcb.tee, rtcb.boot_loader
    // );
    // eprintln!(
    //     "ARPT current  TCB version: ucodeSPL={}&snpSPL={}&teeSPL={}&blSPL={}",
    //     ctcb.microcode, ctcb.snp, ctcb.tee, ctcb.boot_loader
    // );
    // eprintln!(
    //     "VCEK          TCB version: ucodeSPL={}&snpSPL={}&teeSPL={}&blSPL={}",
    //     vtcb.microcode, vtcb.snp, vtcb.tee, vtcb.boot_loader
    // );

    let actual_chip_id = report.data.chip_id;
    let expected_chip_id = chip_id(vcek)?;
    // eprintln!("VCEK chip ID: {}", hex::encode(expected_chip_id));
    // eprintln!("ARPT chip ID: {}", hex::encode(actual_chip_id));
    for i in 0..64 {
        if actual_chip_id[i] != expected_chip_id[i] {
            anyhow::bail!("chip id differs {}", i);
        }
    }

    let verifying_key = {
        let pubkey_info = vcek.tbs_certificate.subject_public_key_info.owned_to_ref();
        p384::ecdsa::VerifyingKey::from_sec1_bytes(pubkey_info.subject_public_key.raw_bytes())
            .map_err(|_err| anyhow::anyhow!("could not extract ECDSA P-384 public key"))
    }?;
    let message = report.data.as_bytes();

    // Only the first 48 bytes of r and s make up p384::ecdsa::Signature,
    // the rest is headroom to allow longer signatures as well.
    let mut rr: [u8; 48] = [0; 48];
    let mut ss: [u8; 48] = [0; 48];
    rr.copy_from_slice(&report.signature.r[0..48]);
    ss.copy_from_slice(&report.signature.s[0..48]);
    let signature = p384::ecdsa::Signature::from_scalars(rr, ss)
        .map_err(|_err| anyhow::anyhow!("could not extract ECDSA P-384 signature"))?;

    Ok(verifying_key
        .verify(message, &signature)
        .map_err(|_err| anyhow::anyhow!("failed to verify ECDSA P-384 signature"))?)
}
