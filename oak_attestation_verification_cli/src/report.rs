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

use std::fmt::Write;

use anyhow::anyhow;
use oak_attestation_gcp::{
    jwt::verification::{AttestationTokenVerificationReport, CertificateReport, IssuerReport},
    policy::ConfidentialSpaceVerificationReport,
    policy_generator::confidential_space_policy_from_reference_values,
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
        let policy = confidential_space_policy_from_reference_values(reference_values)?;
        let report =
            policy.report(attestation_timestamp, event, endorsement).map_err(anyhow::Error::msg)?;
        Ok(VerificationReport::ConfidentialSpace(report))
    }

    pub fn print(
        &self,
        writer: &mut impl Write,
        indent: usize,
        handshake_hash: &[u8],
        session_binding: Option<&SessionBinding>,
    ) -> std::fmt::Result {
        match self {
            VerificationReport::ConfidentialSpace(report) => {
                print_confidential_space_attestation_report(writer, indent, report)?;
            }
            VerificationReport::CertificateBased(report) => {
                print_certificate_based_attestation_report(writer, indent, report)?;
            }
        }

        match session_binding {
            None => print_indented!(writer, indent, "❌ No session binding found")?,
            Some(session_binding) => {
                print_indented!(writer, indent, "🔐 Session binding:")?;
                let indent = indent + 1;
                match verify_session_binding(
                    &self.session_binding_public_key(),
                    handshake_hash,
                    &session_binding.binding,
                ) {
                    Ok(()) => print_indented!(writer, indent, "✅ verified successfully")?,
                    Err(err) => print_indented!(writer, indent, "❌ failed to verify: {}", err)?,
                }
            }
        }
        Ok(())
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
    writer: &mut impl Write,
    indent: usize,
    report: &SessionBindingPublicKeyVerificationReport,
) -> std::fmt::Result {
    match &report.endorsement {
        Err(err) => print_indented!(writer, indent, "❌ is invalid: {}", err),
        Ok(certificate_verification_report) => {
            print_certificate_verification_report(writer, indent, certificate_verification_report)
        }
    }
}

fn print_certificate_verification_report(
    writer: &mut impl Write,
    indent: usize,
    report: &CertificateVerificationReport,
) -> std::fmt::Result {
    print_indented!(writer, indent, "📜 Certificate:")?;
    let indent = indent + 1;
    let CertificateVerificationReport { validity, verification, freshness: freshness_option } =
        report;
    match validity {
        Err(err) => print_indented!(writer, indent, "❌ is invalid: {}", err)?,
        Ok(()) => print_indented!(writer, indent, "✅ is valid")?,
    }
    match verification {
        Err(err) => print_indented!(writer, indent, "❌ failed to verify: {}", err)?,
        Ok(()) => print_indented!(writer, indent, "✅ verified successfully")?,
    }
    if let Some(freshness) = freshness_option {
        match freshness {
            Err(err) => {
                print_indented!(writer, indent, "❌ proof of freshness failed to verify: {}", err)?
            }
            Ok(()) => print_indented!(writer, indent, "✅ is fresh")?,
        }
    }
    Ok(())
}

fn print_confidential_space_attestation_report(
    writer: &mut impl Write,
    indent: usize,
    report: &ConfidentialSpaceVerificationReport,
) -> std::fmt::Result {
    print_indented!(writer, indent, "🔑 Public key:")?;
    {
        let indent = indent + 1;
        match &report.public_key_verification {
            Err(err) => print_indented!(writer, indent, "❌ failed to verify: {}", err)?,
            Ok(()) => print_indented!(writer, indent, "✅ verified successfully")?,
        }
    }
    print_token_report(writer, indent, &report.token_report)?;
    print_indented!(writer, indent, "📦 Workload endorsement:")?;
    {
        let indent = indent + 1;
        match &report.workload_endorsement_verification {
            None => print_indented!(writer, indent, "🤷 not present")?,
            Some(Err(err)) => print_indented!(writer, indent, "❌ failed to verify: {}", err)?,
            Some(Ok(())) => print_indented!(writer, indent, "✅ verified successfully")?,
        }
    }
    Ok(())
}

fn print_token_report(
    writer: &mut impl Write,
    indent: usize,
    report: &AttestationTokenVerificationReport,
) -> std::fmt::Result {
    print_indented!(writer, indent, "🪙 Token verification:")?;
    let indent = indent + 1;
    let AttestationTokenVerificationReport {
        has_required_claims,
        validity,
        verification,
        issuer_report,
    } = report;
    match has_required_claims {
        Err(err) => print_indented!(writer, indent, "❌ failed to have required claims: {}", err)?,
        Ok(()) => print_indented!(writer, indent, "✅ has required claims")?,
    }
    match validity {
        Err(err) => print_indented!(writer, indent, "❌ is invalid: {}", err)?,
        Ok(()) => print_indented!(writer, indent, "✅ is valid")?,
    }
    match verification {
        Err(err) => print_indented!(writer, indent, "❌ failed to verify: {}", err)?,
        Ok(_) => print_indented!(writer, indent, "✅ verified successfully")?,
    }
    print_indented!(writer, indent, "📜 Certificate chain:")?;
    print_certificate_chain(writer, indent + 1, issuer_report)
}

fn print_certificate_chain(
    writer: &mut impl Write,
    indent: usize,
    report: &Result<
        CertificateReport,
        oak_attestation_gcp::jwt::verification::AttestationVerificationError,
    >,
) -> std::fmt::Result {
    match report {
        Err(err) => print_indented!(writer, indent, "❌ invalid: {}", err),
        Ok(report) => {
            print_indented!(writer, indent, "📜 Certificate:")?;
            {
                let indent = indent + 1;
                match &report.validity {
                    Err(err) => print_indented!(writer, indent, "❌ is invalid: {}", err)?,
                    Ok(()) => print_indented!(writer, indent, "✅ is valid")?,
                }
                match &report.verification {
                    Err(err) => print_indented!(writer, indent, "❌ failed to verify: {}", err)?,
                    Ok(()) => print_indented!(writer, indent, "✅ verified successfully")?,
                }
                print_indented!(writer, indent, "✍️ issued by:")?;
            }
            match report.issuer_report.as_ref() {
                IssuerReport::OtherCertificate(report) => {
                    print_certificate_chain(writer, indent, report)
                }
                IssuerReport::Root => {
                    print_indented!(writer, indent, "🛡️ Confidential Space root certificate")
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

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use jwt::{
        algorithm::{openssl::PKeyWithDigest, AlgorithmType},
        SignWithKey, SigningAlgorithm, Token, Verified, VerifyWithKey, VerifyingAlgorithm,
    };
    use oak_attestation_gcp::{
        jwt::{
            verification::{
                AttestationTokenVerificationReport, AttestationVerificationError,
                CertificateReport, IssuerReport,
            },
            Claims, Header,
        },
        policy::{ConfidentialSpaceVerificationError, ConfidentialSpaceVerificationReport},
    };
    use oak_attestation_verification::SessionBindingPublicKeyVerificationReport;
    use oak_crypto::certificate::certificate_verifier::{
        CertificateVerificationError, CertificateVerificationReport,
    };
    use openssl::{hash::MessageDigest, pkey::PKey, rsa::Rsa};
    use p256::ecdsa::{signature::SignerMut, Signature, SigningKey};

    use super::*;

    const INDENT: usize = 0;

    // This is a test-only key.
    const SIGNING_KEY: &str = "
-----BEGIN PRIVATE KEY-----
MIGHAgEAMBMGByqGSM49AgEGCCqGSM49AwEHBG0wawIBAQQgrvnMHLTorFFIv81o
tY7X8XNBXwBH9yNp9Nza8ymFRbmhRANCAAShmAYmC7YQ2SHOzTaugBQDSVQrjwnh
Nj98VHCkMOChdP0NoY0+ASi3S9WesDHql/SS3TeVKIW0W7VRIYDz51rU
-----END PRIVATE KEY-----
";
    const HANDSHAKE_HASH: &[u8] = b"abc123def";

    // TODO: b/419209669 - Add test cases for the VerificationReport constructor
    // methods.

    #[test]
    fn test_print_certificate_based_report_success() {
        let mut signing_key = SigningKey::from_str(SIGNING_KEY).unwrap();
        let handshake_signature: Signature = signing_key.sign(HANDSHAKE_HASH);

        let report =
            VerificationReport::CertificateBased(SessionBindingPublicKeyVerificationReport {
                endorsement: Ok(CertificateVerificationReport {
                    validity: Ok(()),
                    verification: Ok(()),
                    freshness: Some(Ok(())),
                }),
                session_binding_public_key: signing_key.verifying_key().to_sec1_bytes().to_vec(),
            });
        let mut writer = String::new();
        report
            .print(
                &mut writer,
                INDENT,
                HANDSHAKE_HASH,
                Option::Some(&session_binding(&handshake_signature.to_bytes())),
            )
            .unwrap();
        assert_eq_trimmed_lines(
            &writer,
            &[
                "📜 Certificate:",
                "✅ is valid",
                "✅ verified successfully",
                "✅ is fresh",
                "🔐 Session binding:",
                "✅ verified successfully",
            ],
        );
    }

    #[test]
    fn test_print_certificate_based_report_endorsement_error_no_binding() {
        let report =
            VerificationReport::CertificateBased(SessionBindingPublicKeyVerificationReport {
                endorsement: Err(CertificateVerificationError::UnknownError("endorsement error")),
                session_binding_public_key: vec![],
            });
        let mut writer = String::new();
        report.print(&mut writer, INDENT, HANDSHAKE_HASH, Option::None).unwrap();
        assert_eq_trimmed_lines(
            &writer,
            &["❌ is invalid: Unknown error: endorsement error", "❌ No session binding found"],
        );
    }

    #[test]
    fn test_print_certificate_based_report_certificate_verification_session_binding_errors() {
        let signing_key = SigningKey::from_str(SIGNING_KEY).unwrap();

        let report =
            VerificationReport::CertificateBased(SessionBindingPublicKeyVerificationReport {
                endorsement: Ok(CertificateVerificationReport {
                    validity: Err(CertificateVerificationError::UnknownError("validity error")),
                    verification: Err(CertificateVerificationError::UnknownError(
                        "verification error",
                    )),
                    freshness: Some(Err(CertificateVerificationError::UnknownError(
                        "freshness error",
                    ))),
                }),
                session_binding_public_key: signing_key.verifying_key().to_sec1_bytes().to_vec(),
            });
        let mut writer = String::new();
        report
            .print(
                &mut writer,
                INDENT,
                HANDSHAKE_HASH,
                Option::Some(&session_binding("nonsense".as_bytes())),
            )
            .unwrap();
        assert_eq_trimmed_lines(
            &writer,
            &[
                "📜 Certificate:",
                "❌ is invalid: Unknown error: validity error",
                "❌ failed to verify: Unknown error: verification error",
                "❌ proof of freshness failed to verify: Unknown error: freshness error",
                "🔐 Session binding:",
                "❌ failed to verify: could not parse signature",
            ],
        );
    }

    #[test]
    fn test_print_confidential_space_report_success() {
        let mut signing_key = SigningKey::from_str(SIGNING_KEY).unwrap();
        let handshake_signature: Signature = signing_key.sign(HANDSHAKE_HASH);

        let report = VerificationReport::ConfidentialSpace(ConfidentialSpaceVerificationReport {
            public_key_verification: Ok(()),
            token_report: AttestationTokenVerificationReport {
                has_required_claims: Ok(()),
                validity: Ok(()),
                verification: Ok(generate_verified_token().unwrap()),
                issuer_report: Ok(CertificateReport {
                    validity: Ok(()),
                    verification: Ok(()),
                    issuer_report: Box::new(IssuerReport::Root),
                }),
            },
            workload_endorsement_verification: Some(Ok(())),
            session_binding_public_key: signing_key.verifying_key().to_sec1_bytes().to_vec(),
        });

        let mut writer = String::new();
        report
            .print(
                &mut writer,
                INDENT,
                HANDSHAKE_HASH,
                Option::Some(&session_binding(&handshake_signature.to_bytes())),
            )
            .unwrap();
        assert_eq_trimmed_lines(
            &writer,
            &[
                "🔑 Public key:",
                "✅ verified successfully",
                "🪙 Token verification:",
                "✅ has required claims",
                "✅ is valid",
                "✅ verified successfully",
                "📜 Certificate chain:",
                "📜 Certificate:",
                "✅ is valid",
                "✅ verified successfully",
                "✍️ issued by:",
                "🛡️ Confidential Space root certificate",
                "📦 Workload endorsement:",
                "✅ verified successfully",
                "🔐 Session binding:",
                "✅ verified successfully",
            ],
        );
    }

    #[test]
    fn test_print_confidential_space_report_success_no_workload_endorsement_no_binding() {
        let report = VerificationReport::ConfidentialSpace(ConfidentialSpaceVerificationReport {
            public_key_verification: Ok(()),
            token_report: AttestationTokenVerificationReport {
                has_required_claims: Ok(()),
                validity: Ok(()),
                verification: Ok(generate_verified_token().unwrap()),
                issuer_report: Ok(CertificateReport {
                    validity: Ok(()),
                    verification: Ok(()),
                    issuer_report: Box::new(IssuerReport::Root),
                }),
            },
            workload_endorsement_verification: None,
            session_binding_public_key: vec![],
        });

        let mut writer = String::new();
        report.print(&mut writer, INDENT, HANDSHAKE_HASH, Option::None).unwrap();
        assert_eq_trimmed_lines(
            &writer,
            &[
                "🔑 Public key:",
                "✅ verified successfully",
                "🪙 Token verification:",
                "✅ has required claims",
                "✅ is valid",
                "✅ verified successfully",
                "📜 Certificate chain:",
                "📜 Certificate:",
                "✅ is valid",
                "✅ verified successfully",
                "✍️ issued by:",
                "🛡️ Confidential Space root certificate",
                "📦 Workload endorsement:",
                "🤷 not present",
                "❌ No session binding found",
            ],
        );
    }

    #[test]
    fn test_print_confidential_space_report_errors() {
        let signing_key = SigningKey::from_str(SIGNING_KEY).unwrap();

        let report = VerificationReport::ConfidentialSpace(ConfidentialSpaceVerificationReport {
            public_key_verification: Err(ConfidentialSpaceVerificationError::MissingField(
                "public key",
            )),
            token_report: AttestationTokenVerificationReport {
                has_required_claims: Err(AttestationVerificationError::UnknownError("debug image")),
                validity: Err(AttestationVerificationError::UnknownError("token validity error")),
                verification: Err(AttestationVerificationError::UnknownError("verification error")),
                issuer_report: Err(AttestationVerificationError::UnknownError("issuer error")),
            },
            workload_endorsement_verification: Some(Err(
                ConfidentialSpaceVerificationError::EndorsementVerificationError(
                    "endorsement verification error".to_string(),
                ),
            )),
            session_binding_public_key: signing_key.verifying_key().to_sec1_bytes().to_vec(),
        });

        let mut writer = String::new();
        report
            .print(
                &mut writer,
                INDENT,
                HANDSHAKE_HASH,
                Option::Some(&session_binding("nonsense".as_bytes())),
            )
            .unwrap();
        assert_eq_trimmed_lines(
            &writer,
            &[
                "🔑 Public key:",
                "❌ failed to verify: Missing field: public key",
                "🪙 Token verification:",
                "❌ failed to have required claims: Unknown error: debug image",
                "❌ is invalid: Unknown error: token validity error",
                "❌ failed to verify: Unknown error: verification error",
                "📜 Certificate chain:",
                "❌ invalid: Unknown error: issuer error",
                "📦 Workload endorsement:",
                "❌ failed to verify: Failed to verify endorsement: endorsement verification error",
                "🔐 Session binding:",
                "❌ failed to verify: could not parse signature",
            ],
        );
    }

    #[test]
    fn test_print_confidential_space_report_statement_rekor_errors() {
        let mut signing_key = SigningKey::from_str(SIGNING_KEY).unwrap();
        let handshake_signature: Signature = signing_key.sign(HANDSHAKE_HASH);

        let report = VerificationReport::ConfidentialSpace(ConfidentialSpaceVerificationReport {
            public_key_verification: Ok(()),
            token_report: AttestationTokenVerificationReport {
                has_required_claims: Ok(()),
                validity: Ok(()),
                verification: Ok(generate_verified_token().unwrap()),
                issuer_report: Ok(CertificateReport {
                    validity: Ok(()),
                    verification: Ok(()),
                    issuer_report: Box::new(IssuerReport::Root),
                }),
            },
            workload_endorsement_verification: Some(Err(
                ConfidentialSpaceVerificationError::EndorsementVerificationError(
                    "endorsement verification error".to_string(),
                ),
            )),
            session_binding_public_key: signing_key.verifying_key().to_sec1_bytes().to_vec(),
        });

        let mut writer = String::new();
        report
            .print(
                &mut writer,
                INDENT,
                HANDSHAKE_HASH,
                Option::Some(&session_binding(&handshake_signature.to_bytes())),
            )
            .unwrap();
        assert_eq_trimmed_lines(
            &writer,
            &[
                "🔑 Public key:",
                "✅ verified successfully",
                "🪙 Token verification:",
                "✅ has required claims",
                "✅ is valid",
                "✅ verified successfully",
                "📜 Certificate chain:",
                "📜 Certificate:",
                "✅ is valid",
                "✅ verified successfully",
                "✍️ issued by:",
                "🛡️ Confidential Space root certificate",
                "📦 Workload endorsement:",
                "❌ failed to verify: Failed to verify endorsement: endorsement verification error",
                "🔐 Session binding:",
                "✅ verified successfully",
            ],
        );
    }

    /// Asserts that the (trimmed) lines in [actual] are equal to those in
    /// [expected].
    fn assert_eq_trimmed_lines(actual: &str, expected: &[&str]) {
        let lines: Vec<&str> = actual
            .split("\n")
            .map(|line| line.trim())
            .filter(|line| !line.trim().is_empty())
            .collect();
        assert_eq!(lines.as_slice(), expected);
    }

    fn session_binding(session_binding: &[u8]) -> SessionBinding {
        SessionBinding { binding: session_binding.to_vec() }
    }

    fn generate_verified_token() -> anyhow::Result<Token<Header, Claims, Verified>> {
        let key: PKey<openssl::pkey::Private> = PKey::from_rsa(Rsa::generate(2048)?)?;
        let private_key = PKeyWithDigest { digest: MessageDigest::sha256(), key: key.clone() };
        let public_key = PKeyWithDigest {
            digest: MessageDigest::sha256(),
            key: PKey::public_key_from_pem(key.public_key_to_pem()?.as_slice())?,
        };
        let header = Header { algorithm: AlgorithmType::Rs256, x509_chain: vec![] };
        let claims = Claims { ..Default::default() };
        let signed_token = Token::new(header, claims)
            .sign_with_key(&Rs256PKeyWithDigest { delegate: private_key })?;
        let unverified_token: Token<Header, Claims, _> =
            Token::parse_unverified(signed_token.as_str())?;
        Ok(unverified_token.verify_with_key(&Rs256PKeyWithDigest { delegate: public_key })?)
    }

    // This is a hack, and _shouldn't_ be necessary.
    // https://github.com/mikkyang/rust-jwt/blob/47e8fbb/src/token/verified.rs#L171-L194
    // shows an example of the jwt crate doing the same as the code above
    // (generating a token, signing it, and verifying it), but I cannot get this
    // to work. No matter how I generate a key, the error at
    // https://github.com/mikkyang/rust-jwt/blob/47e8fbb/src/algorithm/openssl.rs#L44
    // is thrown, apparently because the key ID never gets set correctly.
    // So instead, we have this hack to completely override the algorithm_type()
    // function.
    struct Rs256PKeyWithDigest<T> {
        delegate: PKeyWithDigest<T>,
    }

    impl SigningAlgorithm for Rs256PKeyWithDigest<openssl::pkey::Private> {
        fn algorithm_type(&self) -> AlgorithmType {
            AlgorithmType::Rs256
        }
        fn sign(&self, header: &str, claims: &str) -> Result<String, jwt::error::Error> {
            self.delegate.sign(header, claims)
        }
    }

    impl VerifyingAlgorithm for Rs256PKeyWithDigest<openssl::pkey::Public> {
        fn algorithm_type(&self) -> AlgorithmType {
            AlgorithmType::Rs256
        }
        fn verify_bytes(
            &self,
            header: &str,
            claims: &str,
            signature: &[u8],
        ) -> Result<bool, jwt::error::Error> {
            self.delegate.verify_bytes(header, claims, signature)
        }
    }
}
