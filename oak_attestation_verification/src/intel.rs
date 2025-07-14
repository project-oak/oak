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

use anyhow::{anyhow, Context};
use const_oid::db::rfc5912::ECDSA_WITH_SHA_256;
use oak_tdx_quote::QeCertificationData;
use p256::ecdsa::{signature::Verifier, Signature, VerifyingKey};
use x509_cert::{
    der::{referenced::OwnedToRef, DecodePem, Encode},
    Certificate,
};

const PCK_ROOT: &str = include_str!("../data/Intel_SGX_Provisioning_Certification_RootCA.pem");

#[allow(unused)]
fn verify_quote_cert_chain_and_extract_leaf(
    certification_data: &QeCertificationData,
) -> anyhow::Result<Certificate> {
    let mut certificates = if let &QeCertificationData::PckCertChain(chain) = certification_data {
        Ok(Certificate::load_pem_chain(chain)
            .map_err(anyhow::Error::msg)
            .context("couldn't parse certificate chain")?)
    } else {
        Err(anyhow!("certification data is not a PCK certificate chain"))
    }?;
    // The PCK certificate chain includes the root certificate, but we want to make
    // sure it matches the actual root certificate that was published. So we replace
    // the provided root certificate with the actual published one.
    certificates.pop().ok_or_else(|| anyhow!("certificate chain is empty"))?;
    let root = Certificate::from_pem(PCK_ROOT.as_bytes())
        .map_err(anyhow::Error::msg)
        .context("couldn't parse known root certificate")?;
    certificates.push(root);
    let mut chain = certificates.iter();
    let mut signee = chain.next().ok_or_else(|| anyhow!("certificate chain is empty"))?;
    let leaf = signee.clone();
    // Each certificate must be signed by the next one in the chain.
    for signer in chain {
        verify_ecdsa_cert_signature(signer, signee).context("certificate chain is not valid")?;
        signee = signer;
    }
    Ok(leaf)
}

fn verify_ecdsa_cert_signature(signer: &Certificate, signee: &Certificate) -> anyhow::Result<()> {
    anyhow::ensure!(
        signee.signature_algorithm.oid == ECDSA_WITH_SHA_256,
        "unsupported signature algorithm: {:?}",
        signee.signature_algorithm
    );

    let verifying_key = {
        let pubkey_info = signer.tbs_certificate.subject_public_key_info.owned_to_ref();
        VerifyingKey::from_sec1_bytes(pubkey_info.subject_public_key.raw_bytes())
            .map_err(|_err| anyhow::anyhow!("could not parse ECDSA P256 public key"))?
    };

    let message = signee
        .tbs_certificate
        .to_der()
        .map_err(|_err| anyhow::anyhow!("could not extract message to verify signature"))?;
    let signature = Signature::from_der(signee.signature.raw_bytes())
        .map_err(|_err| anyhow::anyhow!("could not extract signature"))?;

    verifying_key
        .verify(&message, &signature)
        .map_err(|_err| anyhow::anyhow!("signature verification failed"))
}

#[cfg(test)]
mod tests;
