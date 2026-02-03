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

use const_oid::db::rfc5912::{ECDSA_WITH_SHA_256, ID_RSASSA_PSS};
use oak_time::Instant;
use p256::ecdsa::{Signature as P256Signature, VerifyingKey as P256VerifyingKey};
use rsa::{RsaPublicKey, pss::Signature as RsaSignature, signature::Verifier};
use sha2::Sha384;
use x509_cert::{
    Certificate,
    der::{Encode, referenced::OwnedToRef},
};

/// Verifies that the `signee` certificate is correctly signed by the `signer`.
pub fn verify_cert_signature(signer: &Certificate, signee: &Certificate) -> anyhow::Result<()> {
    let message = signee
        .tbs_certificate
        .to_der()
        .map_err(|_err| anyhow::anyhow!("could not extract message to verify RSA signature"))?;
    let signature_bytes = signee.signature.raw_bytes();

    match signee.signature_algorithm.oid {
        ID_RSASSA_PSS => {
            let verifying_key = {
                let pubkey_info = signer.tbs_certificate.subject_public_key_info.owned_to_ref();
                let pubkey = RsaPublicKey::try_from(pubkey_info)
                    .map_err(|_err| anyhow::anyhow!("could not parse RSA public key"))?;
                rsa::pss::VerifyingKey::<Sha384>::new(pubkey)
            };
            let signature = RsaSignature::try_from(signature_bytes)
                .map_err(|_err| anyhow::anyhow!("could not extract RSA signature"))?;
            verifying_key
                .verify(&message, &signature)
                .map_err(|_err| anyhow::anyhow!("signature verification failed"))
        }
        ECDSA_WITH_SHA_256 => {
            let verifying_key: P256VerifyingKey = signer
                .tbs_certificate
                .subject_public_key_info
                .owned_to_ref()
                .try_into()
                .map_err(|_err| anyhow::anyhow!("could not extract ECDSA P-384 public key"))?;
            let signature = P256Signature::from_der(signature_bytes)
                .map_err(|_err| anyhow::anyhow!("could not extract NIST P-256 ECDSA signature"))?;
            verifying_key
                .verify(&message, &signature)
                .map_err(|_err| anyhow::anyhow!("signature verification failed"))
        }
        _ => Err(anyhow::anyhow!(
            "unsupported signature algorithm: {:?}",
            signee.signature_algorithm
        )),
    }
}

/// Checks whether a certificate is considered valid at the specified time.
pub fn check_certificate_validity(
    verification_time: Instant,
    cert: &Certificate,
) -> anyhow::Result<()> {
    let start_time = Instant::from_unix_nanos(
        cert.tbs_certificate.validity.not_before.to_unix_duration().as_nanos() as i128,
    );
    let end_time = Instant::from_unix_nanos(
        cert.tbs_certificate.validity.not_after.to_unix_duration().as_nanos() as i128,
    );
    if verification_time < start_time {
        anyhow::bail!("certificate is not yet valid");
    }
    if verification_time > end_time {
        anyhow::bail!("certificate is expired");
    }
    Ok(())
}
