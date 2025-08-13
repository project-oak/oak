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

use anyhow::anyhow;
use oak_attestation_gcp::{
    cosign::{CosignReferenceValues, CosignVerificationReport, StatementReport},
    jwt::verification::{AttestationTokenVerificationReport, CertificateReport, IssuerReport},
    policy::{ConfidentialSpacePolicy, ConfidentialSpaceVerificationReport},
};
use oak_attestation_verification::{
    SessionBindingPublicKeyPolicy, SessionBindingPublicKeyVerificationReport,
};
use oak_crypto::certificate::certificate_verifier::{
    CertificateVerificationReport, CertificateVerifier,
};
use oak_crypto_tink::signature_verifier::SignatureVerifier;
use oak_proto_rust::oak::{
    attestation::v1::{CertificateBasedReferenceValues, ConfidentialSpaceReferenceValues},
    session::v1::SessionBinding,
    Variant,
};
use oak_session::session_binding::{SessionBindingVerifier, SignatureBindingVerifierBuilder};
use oak_time::Instant;
use p256::ecdsa::VerifyingKey;
use x509_cert::{der::DecodePem, Certificate};

use crate::print::print_indented;

pub enum VerificationReport {
    CertificateBased(SessionBindingPublicKeyVerificationReport),
    ConfidentialSpace(ConfidentialSpaceVerificationReport),
}

impl VerificationReport {
    pub fn certificate_based(
        reference_values: &CertificateBasedReferenceValues,
        attestation_timestamp: Instant,
        event: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<VerificationReport> {
        let policy = {
            let tink_public_keyset =
                reference_values.clone().ca.unwrap_or_default().tink_proto_keyset;
            let signature_verifier = SignatureVerifier::new(tink_public_keyset.as_slice());
            let certificate_verifier = CertificateVerifier::new(signature_verifier);
            SessionBindingPublicKeyPolicy::new(certificate_verifier)
        };
        let report =
            policy.report(attestation_timestamp, event, endorsement).map_err(anyhow::Error::msg)?;
        Ok(VerificationReport::CertificateBased(report))
    }

    pub fn confidential_space(
        reference_values: &ConfidentialSpaceReferenceValues,
        attestation_timestamp: Instant,
        event: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<VerificationReport> {
        let policy = {
            let root_certificate = Certificate::from_pem(&reference_values.root_certificate_pem)
                .map_err(anyhow::Error::msg)?;
            let cosign_reference_values = CosignReferenceValues::from_proto(
                &reference_values.cosign_reference_values.clone().unwrap_or_default(),
            )
            .map_err(anyhow::Error::msg)?;
            ConfidentialSpacePolicy::new(root_certificate, cosign_reference_values)
        };
        let report =
            policy.report(attestation_timestamp, event, endorsement).map_err(anyhow::Error::msg)?;
        Ok(VerificationReport::ConfidentialSpace(report))
    }

    pub fn print(
        &self,
        indent: usize,
        handshake_hash: &[u8],
        session_binding: Option<&SessionBinding>,
    ) {
        match self {
            VerificationReport::ConfidentialSpace(report) => {
                print_confidential_space_attestation_report(indent, report)
            }
            VerificationReport::CertificateBased(report) => {
                print_certificate_based_attestation_report(indent, report)
            }
        }

        let indent = indent + 1;
        match session_binding {
            None => print_indented!(indent, "❌ No session binding found"),
            Some(session_binding) => {
                print_indented!(indent, "🔐 Session binding:");
                let indent = indent + 1;
                match verify_session_binding(
                    &self.session_binding_public_key(),
                    handshake_hash,
                    &session_binding.binding,
                ) {
                    Ok(()) => print_indented!(indent, "✅ verified successfully"),
                    Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
                }
            }
        }
    }

    fn session_binding_public_key(&self) -> Vec<u8> {
        match self {
            VerificationReport::ConfidentialSpace(report) => {
                report.session_binding_public_key.clone()
            }
            VerificationReport::CertificateBased(report) => {
                report.session_binding_public_key.clone()
            }
        }
    }
}

fn print_certificate_based_attestation_report(
    indent: usize,
    report: &SessionBindingPublicKeyVerificationReport,
) {
    match &report.endorsement {
        Err(err) => print_indented!(indent, "❌ is invalid: {}", err),
        Ok(certificate_verification_report) => {
            print_certificate_verification_report(indent, certificate_verification_report)
        }
    }
}

fn print_certificate_verification_report(indent: usize, report: &CertificateVerificationReport) {
    print_indented!(indent, "📜 Certificate:");
    let indent = indent + 1;
    let CertificateVerificationReport { validity, verification, freshness: freshness_option } =
        report;
    match validity {
        Err(err) => print_indented!(indent, "❌ is invalid: {}", err),
        Ok(()) => print_indented!(indent, "✅ is valid"),
    }
    match verification {
        Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
        Ok(()) => print_indented!(indent, "✅ verified successfully"),
    }
    if let Some(freshness) = freshness_option {
        match freshness {
            Err(err) => print_indented!(indent, "❌ proof of freshness failed to verify: {}", err),
            Ok(()) => print_indented!(indent, "✅ is fresh"),
        }
    }
}

fn print_confidential_space_attestation_report(
    indent: usize,
    report: &ConfidentialSpaceVerificationReport,
) {
    print_indented!(indent, "🔑 Public key:");
    {
        let indent = indent + 1;
        match &report.public_key_verification {
            Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
            Ok(()) => print_indented!(indent, "✅ verified successfully"),
        }
    }
    print_token_report(indent, &report.token_report);
    print_indented!(indent, "📦 Workload endorsement:");
    {
        let indent = indent + 1;
        match &report.workload_endorsement_verification {
            None => print_indented!(indent, "🤷 not present"),
            Some(Err(err)) => print_indented!(indent, "❌ failed to verify: {}", err),
            Some(Ok(CosignVerificationReport { statement_verification })) => {
                print_indented!(indent, " Statement");
                let indent = indent + 1;
                match statement_verification {
                    Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
                    Ok(StatementReport { statement_validation, rekor_verification }) => {
                        match statement_validation {
                            Err(err) => print_indented!(indent, "❌ is invalid: {}", err),
                            Ok(()) => print_indented!(indent, "✅ is valid"),
                        }
                        match rekor_verification {
                            None => print_indented!(indent, "🤷 not verified"),
                            Some(Err(err)) => {
                                print_indented!(indent, "❌ failed to verify: {}", err)
                            }
                            Some(Ok(())) => print_indented!(indent, "✅ verified successfully"),
                        }
                    }
                }
            }
        }
    }
}

fn print_token_report(indent: usize, report: &AttestationTokenVerificationReport) {
    print_indented!(indent, "🪙 Token verification:");
    let indent = indent + 1;
    let AttestationTokenVerificationReport { validity, verification, issuer_report } = report;
    match validity {
        Err(err) => print_indented!(indent, "❌ is invalid: {}", err),
        Ok(()) => print_indented!(indent, "✅ is valid"),
    }
    match verification {
        Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
        Ok(_) => print_indented!(indent, "✅ verified successfully"),
    }
    print_indented!(indent, "📜 Certificate chain:");
    print_certificate_chain(indent + 1, issuer_report);
}

fn print_certificate_chain(
    indent: usize,
    report: &Result<
        CertificateReport,
        oak_attestation_gcp::jwt::verification::AttestationVerificationError,
    >,
) {
    match report {
        Err(err) => print_indented!(indent, "❌ invalid: {}", err),
        Ok(report) => {
            print_indented!(indent, "📜 Certificate:");
            {
                let indent = indent + 1;
                match &report.validity {
                    Err(err) => print_indented!(indent, "❌ is invalid: {}", err),
                    Ok(()) => print_indented!(indent, "✅ is valid"),
                }
                match &report.verification {
                    Err(err) => print_indented!(indent, "❌ failed to verify: {}", err),
                    Ok(()) => print_indented!(indent, "✅ verified successfully"),
                }
                print_indented!(indent, "✍️  issued by:");
            }
            match report.issuer_report.as_ref() {
                IssuerReport::OtherCertificate(report) => {
                    print_certificate_chain(indent, report);
                }
                IssuerReport::Root => {
                    print_indented!(indent, "🛡️ Confidential Space root certificate");
                }
            }
        }
    }
}

fn verify_session_binding(
    session_binding_public_key: &[u8],
    handshake_hash: &[u8],
    binding: &[u8],
) -> anyhow::Result<()> {
    let verifying_key = VerifyingKey::from_sec1_bytes(session_binding_public_key)
        .map_err(|err| anyhow!("VerifyingKey construction failed: {}", err))?;
    let verifier = SignatureBindingVerifierBuilder::default()
        .verifier(Box::new(verifying_key))
        .build()
        .map_err(|err| anyhow!("SignatureBindingVerifier construction failed: {}", err))?;
    verifier.verify_binding(handshake_hash, binding)
}
