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

use alloc::fmt;

use base64::{engine::general_purpose::STANDARD, Engine};
use jwt::{Token, Unverified, Verified, VerifyWithKey};
use oak_time::Instant;
use x509_cert::{der::Decode, Certificate};
use x509_verify::VerifyingKey;

use crate::jwt::{algorithm::CertificateAlgorithm, Claims, Header};

#[derive(thiserror::Error, Debug)]
pub enum AttestationVerificationError {
    #[error("Failed to verify JWT: {0}")]
    JWTError(#[from] jwt::Error),
    #[error("Failed to decode x5c: {0}")]
    X5CDecodeError(#[from] serde_json::Error),
    #[error("Failed to verify certificate: {0}")]
    X509VerificationError(x509_verify::Error),
    #[error("Failed to decode base64: {0}")]
    X509Base64DecodeError(#[from] base64::DecodeError),
    #[error("Failed to decode der: {0}")]
    X509DerDecodeError(x509_cert::der::Error),
    #[error("Certificate validity not_before: {not_before} > {current_time}")]
    X509ValidityNotBefore { not_before: Instant, current_time: Instant },
    #[error("Certificate validity not_after: {not_after} > {current_time}")]
    X509ValidityNotAfter { not_after: Instant, current_time: Instant },
    #[error("Token validity nbf: {nbf} > {current_time}")]
    JWTValidityNotBefore { nbf: Instant, current_time: Instant },
    #[error("Token validity exp: {exp} < {current_time}")]
    JWTValidityExpiration { exp: Instant, current_time: Instant },
    #[error("Empty X509 certificate chain")]
    EmptyX509Chain,
    #[error("Invalid debug status: want {want}, got {got}")]
    InvalidDebugStatus { want: &'static str, got: String },
    #[error("Invalid software name: want {want}, got {got}")]
    InvalidSoftwareName { want: &'static str, got: String },
    #[error("{want} is a required software attribute, but only got {got:?}")]
    MissingRequiredSupportAttribute { want: &'static str, got: Vec<String> },
    #[error("Unknown error: {0}")]
    UnknownError(&'static str),
}

// Convenience From implementations for errors that don't implement
// std::error::Error.

impl From<x509_verify::Error> for AttestationVerificationError {
    fn from(e: x509_verify::Error) -> AttestationVerificationError {
        AttestationVerificationError::X509VerificationError(e)
    }
}

impl From<x509_cert::der::Error> for AttestationVerificationError {
    fn from(e: x509_cert::der::Error) -> AttestationVerificationError {
        AttestationVerificationError::X509DerDecodeError(e)
    }
}

/// Verifies the JWT attestation token from Confidential Space using the
/// provided root certificate.
///
/// The token is verified by checking the signature and the x5c chain in the
/// token against the provided root certificate.
pub fn verify_attestation_token(
    token: Token<Header, Claims, Unverified>,
    root: &Certificate,
    current_time: &oak_time::Instant,
) -> Result<Token<Header, Claims, Verified>, AttestationVerificationError> {
    report_attestation_token(token, root, current_time).into_checked_token()
}

/// Contains the results of (as complete as possible) verification of a JWT.
pub struct AttestationTokenVerificationReport {
    // Whether or not the token was produced using a production image.
    // https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-images#types_of_images
    pub production_image: Result<(), AttestationVerificationError>,
    /// Whether or not the token is valid (with respect to a timestamp).
    pub validity: Result<(), AttestationVerificationError>,
    /// The result of verifying the token (with respect to its signature
    /// issuer).
    pub verification: Result<Token<Header, Claims, Verified>, AttestationVerificationError>,
    /// The result of verifying the token's signature issuer.
    pub issuer_report: Result<CertificateReport, AttestationVerificationError>,
}

impl fmt::Debug for AttestationTokenVerificationReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AttestationTokenVerificationReport")
            .field("validity", &self.validity)
            .field("issuer_report", &self.issuer_report)
            .finish_non_exhaustive()
    }
}

impl AttestationTokenVerificationReport {
    pub fn into_checked_token(
        self,
    ) -> Result<Token<Header, Claims, Verified>, AttestationVerificationError> {
        match self {
            AttestationTokenVerificationReport {
                production_image: Ok(()),
                validity: Ok(()),
                verification: Ok(verified_token),
                issuer_report,
            } => {
                let mut current_report = issuer_report;
                loop {
                    match current_report? {
                        CertificateReport {
                            validity: Ok(()),
                            verification: Ok(()),
                            issuer_report,
                        } => match *issuer_report {
                            IssuerReport::Root => return Ok(verified_token),
                            IssuerReport::OtherCertificate(certificate_report) => {
                                current_report = certificate_report;
                            }
                        },
                        CertificateReport { validity, verification, issuer_report: _ } => {
                            // This matches any non-Ok cases.
                            validity?;
                            verification?;
                            return Err(AttestationVerificationError::UnknownError(
                                "CertificateReport verification failed",
                            ));
                        }
                    }
                }
            }
            AttestationTokenVerificationReport {
                production_image,
                validity,
                verification,
                issuer_report: _,
            } => {
                // This matches any non-Ok cases.
                production_image?;
                validity?;
                verification?;
                Err(AttestationVerificationError::UnknownError(
                    "AttestationTokenVerificationReport verification failed",
                ))
            }
        }
    }
}

#[derive(Debug)]
pub enum IssuerReport {
    /// The result of verifying an issuer which is itself another certificate
    /// in the certificate chain.
    OtherCertificate(Result<CertificateReport, AttestationVerificationError>),
    /// Indicates that the issuer is the root certificate (on which no
    /// verification is performed; because it is necessarily trusted).
    Root,
}

/// Contains the results of verifying a certificate in a certificate chain.
#[derive(Debug)]
pub struct CertificateReport {
    /// Whether or not the certificate is valid (with respect to a timestamp).
    pub validity: Result<(), AttestationVerificationError>,
    /// Whether or not the certificate was verified (using its issuer's
    /// signature).
    pub verification: Result<(), AttestationVerificationError>,
    /// The verification report for the remaining items in the certificate
    /// chain. Wrapped in a [Box] due to the recursive type hierarchy.
    pub issuer_report: Box<IssuerReport>,
}

/// Returns a full report on the success/failure status of verifying the JWT
/// attestation token from Confidential Space using the provided root
/// certificate.
pub fn report_attestation_token(
    token: Token<Header, Claims, Unverified>,
    root: &Certificate,
    current_time: &oak_time::Instant,
) -> AttestationTokenVerificationReport {
    // Construct a chain of certificate verification reports, going
    // through all certificates in the chain.
    // See https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims and https://datatracker.ietf.org/doc/html/rfc7515#section-4.1.6
    // for details of chain ordering. (TL; DR: the certificate used to sign the
    // token is the first in the chain, followed by the certificate used to sign
    // that certificate, and so on until the last certificate, which is signed
    // by the root.)
    let mut issuer = Box::new(root.clone());
    let mut issuer_report = None;
    for base64_der in token.header().x509_chain.iter().rev() {
        issuer_report = Some(
            try {
                let certificate = Box::new(Certificate::from_der(&STANDARD.decode(base64_der)?)?);
                let validity = verify_certificate_validity(certificate.as_ref(), current_time);
                let verification = verify_certificate(issuer.as_ref(), certificate.as_ref());
                issuer = certificate;
                CertificateReport {
                    validity,
                    verification,
                    issuer_report: Box::new(match issuer_report {
                        Some(issuer_report) => IssuerReport::OtherCertificate(issuer_report),
                        None => IssuerReport::Root,
                    }),
                }
            },
        );
    }
    let issuer_report = issuer_report.unwrap_or(Err(AttestationVerificationError::EmptyX509Chain));

    AttestationTokenVerificationReport {
        production_image: verify_production_image(token.claims()),
        validity: verify_token_validity(&token, current_time),
        verification: try {
            // See https://cloud.google.com/confidential-computing/confidential-vm/docs/token-claims#token_items:
            // "Confidential VM supports the RS256 algorithm".
            token.verify_with_key(&CertificateAlgorithm::rs256(issuer.as_ref())?)?
        },
        issuer_report,
    }
}

fn verify_production_image(claims: &Claims) -> Result<(), AttestationVerificationError> {
    // See 'dbgstat' in
    // https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims#top-level_claims.
    if claims.debug_status != "disabled-since-boot" {
        return Err(AttestationVerificationError::InvalidDebugStatus {
            want: "disabled-since-boot",
            got: claims.debug_status.clone(),
        });
    }
    // See 'swname' in
    // https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims#top-level_claims.
    if claims.software_name != "CONFIDENTIAL_SPACE" {
        return Err(AttestationVerificationError::InvalidSoftwareName {
            want: "CONFIDENTIAL_SPACE",
            got: claims.software_name.clone(),
        });
    }
    // See 'support_attributes' in
    // https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims#submods-claims.
    if !claims.submods.confidential_space.support_attributes.contains(&"STABLE".to_string()) {
        return Err(AttestationVerificationError::MissingRequiredSupportAttribute {
            want: "STABLE",
            got: claims.submods.confidential_space.support_attributes.clone(),
        });
    }
    Ok(())
}

fn verify_certificate_validity(
    certificate: &Certificate,
    current_time: &oak_time::Instant,
) -> Result<(), AttestationVerificationError> {
    // TODO: b/427595536 - Need to deduplicate the Validity protos, then
    // this can go away.
    let not_before_nanos =
        certificate.tbs_certificate.validity.not_before.to_unix_duration().as_nanos();
    let not_after_nanos =
        certificate.tbs_certificate.validity.not_after.to_unix_duration().as_nanos();
    let not_before = Instant::from_unix_nanos(
        i128::try_from(not_before_nanos).expect("failed to convert u128 to i128"),
    );
    let not_after = Instant::from_unix_nanos(
        i128::try_from(not_after_nanos).expect("failed to convert u128 to i128"),
    );

    if not_before > *current_time {
        Err(AttestationVerificationError::X509ValidityNotBefore {
            not_before,
            current_time: *current_time,
        })
    } else if *current_time > not_after {
        Err(AttestationVerificationError::X509ValidityNotAfter {
            not_after,
            current_time: *current_time,
        })
    } else {
        Ok(())
    }
}

fn verify_certificate(
    issuer: &Certificate,
    certificate: &Certificate,
) -> Result<(), AttestationVerificationError> {
    VerifyingKey::try_from(issuer)?.verify(certificate)?;
    Ok(())
}

fn verify_token_validity(
    token: &Token<Header, Claims, Unverified>,
    current_time: &oak_time::Instant,
) -> Result<(), AttestationVerificationError> {
    let claims = token.claims();

    if &claims.not_before > current_time {
        Err(AttestationVerificationError::JWTValidityNotBefore {
            nbf: claims.not_before,
            current_time: *current_time,
        })
    } else if current_time > &claims.not_after {
        Err(AttestationVerificationError::JWTValidityExpiration {
            exp: claims.not_after,
            current_time: *current_time,
        })
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use core::assert_matches::assert_matches;
    use std::fs;

    use googletest::prelude::*;
    use jwt::{Token, Unverified};
    use oak_file_utils::data_path;
    use oak_time::{make_instant, Duration, Instant};
    use x509_cert::{der::DecodePem, Certificate};

    use crate::jwt::{
        verification::{
            report_attestation_token, verify_attestation_token, AttestationTokenVerificationReport,
            AttestationVerificationError, CertificateReport, IssuerReport,
        },
        Claims, Header,
    };

    // The time has been set inside the validity interval of the test token.
    fn current_time() -> Instant {
        make_instant!("2025-07-01T17:31:32Z")
    }

    #[test]
    fn validate_token_ok() -> Result<()> {
        let token_str = read_testdata("valid_token.jwt");
        let root = Certificate::from_pem(read_testdata("root_ca_cert.pem"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Claims, Unverified> =
            Token::parse_unverified(&token_str)?;

        verify_attestation_token(unverified_token, &root, &current_time())?;

        Ok(())
    }

    #[test]
    fn report_token_ok() -> Result<()> {
        let token_str = read_testdata("valid_token.jwt");
        let root = Certificate::from_pem(read_testdata("root_ca_cert.pem"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Claims, Unverified> =
            Token::parse_unverified(&token_str)?;

        assert_matches!(
            report_attestation_token(unverified_token, &root, &current_time()),
            AttestationTokenVerificationReport {
                production_image: Ok(()),
                validity: Ok(()),
                verification: Ok(_),
                issuer_report: Ok(CertificateReport {
                    validity: Ok(()),
                    verification: Ok(()),
                    issuer_report: box IssuerReport::OtherCertificate(Ok(CertificateReport {
                        validity: Ok(()),
                        verification: Ok(()),
                        issuer_report: box IssuerReport::Root
                    }))
                })
            }
        );

        Ok(())
    }

    #[test]
    fn validate_token_invalid_signature() -> Result<()> {
        let token_str = read_testdata("invalid_signature_token.jwt");
        let root = Certificate::from_pem(read_testdata("root_ca_cert.pem"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Claims, Unverified> =
            Token::parse_unverified(&token_str)?;

        assert_matches!(
            unsafe {
                verify_attestation_token(unverified_token, &root, &current_time())
                    .unwrap_err_unchecked()
            },
            AttestationVerificationError::JWTError(jwt::Error::InvalidSignature)
        );

        Ok(())
    }

    #[test]
    fn report_token_invalid_signature() -> Result<()> {
        let token_str = read_testdata("invalid_signature_token.jwt");
        let root = Certificate::from_pem(read_testdata("root_ca_cert.pem"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Claims, Unverified> =
            Token::parse_unverified(&token_str)?;

        assert_matches!(
            report_attestation_token(unverified_token, &root, &current_time()),
            AttestationTokenVerificationReport {
                production_image: Ok(()),
                validity: Ok(()),
                verification: Err(AttestationVerificationError::JWTError(
                    jwt::Error::InvalidSignature
                )),
                issuer_report: Ok(CertificateReport {
                    validity: Ok(()),
                    verification: Ok(()),
                    issuer_report: box IssuerReport::OtherCertificate(Ok(CertificateReport {
                        validity: Ok(()),
                        verification: Ok(()),
                        issuer_report: box IssuerReport::Root
                    }))
                })
            }
        );

        Ok(())
    }

    #[test]
    fn validate_token_expired_token() -> Result<()> {
        let token_str = read_testdata("expired_token.jwt");
        let root = Certificate::from_pem(read_testdata("root_ca_cert.pem"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Claims, Unverified> =
            Token::parse_unverified(&token_str)?;

        let result = verify_attestation_token(unverified_token, &root, &current_time());
        let err = unsafe { result.unwrap_err_unchecked() };
        assert_matches!(err, AttestationVerificationError::JWTValidityExpiration { .. });

        Ok(())
    }

    #[test]
    fn report_token_expired_token() -> Result<()> {
        let token_str = read_testdata("expired_token.jwt");
        let root = Certificate::from_pem(read_testdata("root_ca_cert.pem"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Claims, Unverified> =
            Token::parse_unverified(&token_str)?;

        assert_matches!(
            report_attestation_token(unverified_token, &root, &current_time()),
            AttestationTokenVerificationReport {
                production_image: Ok(()),
                validity: Err(AttestationVerificationError::JWTValidityExpiration { .. }),
                verification: Ok(_),
                issuer_report: Ok(CertificateReport {
                    validity: Ok(()),
                    verification: Ok(()),
                    issuer_report: box IssuerReport::OtherCertificate(Ok(CertificateReport {
                        validity: Ok(()),
                        verification: Ok(()),
                        issuer_report: box IssuerReport::Root
                    }))
                })
            }
        );

        Ok(())
    }

    #[test]
    fn validate_token_expired_cert() -> Result<()> {
        let token_str = read_testdata("long_lived_token.jwt");
        let root = Certificate::from_pem(read_testdata("root_ca_cert.pem"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Claims, Unverified> =
            Token::parse_unverified(&token_str)?;

        // Advance the clock by about 2 years
        let expired_current_time = current_time() + Duration::from_seconds(2 * 365 * 24 * 3600);

        assert_matches!(
            unsafe {
                verify_attestation_token(unverified_token, &root, &expired_current_time)
                    .unwrap_err_unchecked()
            },
            AttestationVerificationError::X509ValidityNotAfter { .. }
        );

        Ok(())
    }

    #[test]
    fn report_token_expired_cert() -> Result<()> {
        let token_str = read_testdata("long_lived_token.jwt");
        let root = Certificate::from_pem(read_testdata("root_ca_cert.pem"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Claims, Unverified> =
            Token::parse_unverified(&token_str)?;

        // Advance the clock by about 2 years
        let expired_current_time = current_time() + Duration::from_seconds(2 * 365 * 24 * 3600);

        assert_matches!(
            report_attestation_token(unverified_token, &root, &expired_current_time),
            AttestationTokenVerificationReport {
                production_image: Ok(()),
                validity: Ok(()),
                verification: Ok(_),
                issuer_report: Ok(CertificateReport {
                    validity: Err(AttestationVerificationError::X509ValidityNotAfter { .. }),
                    verification: Ok(()),
                    issuer_report: box IssuerReport::OtherCertificate(Ok(CertificateReport {
                        validity: Ok(()),
                        verification: Ok(()),
                        issuer_report: box IssuerReport::Root
                    }))
                })
            }
        );

        Ok(())
    }

    #[test]
    fn validate_token_debug_token() -> Result<()> {
        let token_str = read_testdata("debug_token.jwt");
        let root = Certificate::from_pem(read_testdata("root_ca_cert.pem"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Claims, Unverified> =
            Token::parse_unverified(&token_str)?;

        let result = verify_attestation_token(unverified_token, &root, &current_time());
        let err = unsafe { result.unwrap_err_unchecked() };
        assert_matches!(err, AttestationVerificationError::InvalidDebugStatus { .. });

        Ok(())
    }

    #[test]
    fn report_token_debug_token() -> Result<()> {
        let token_str = read_testdata("debug_token.jwt");
        let root = Certificate::from_pem(read_testdata("root_ca_cert.pem"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Claims, Unverified> =
            Token::parse_unverified(&token_str)?;

        assert_matches!(
            report_attestation_token(unverified_token, &root, &current_time()),
            AttestationTokenVerificationReport {
                production_image: Err(AttestationVerificationError::InvalidDebugStatus { .. }),
                validity: Ok(()),
                verification: Ok(_),
                issuer_report: Ok(CertificateReport {
                    validity: Ok(()),
                    verification: Ok(()),
                    issuer_report: box IssuerReport::OtherCertificate(Ok(CertificateReport {
                        validity: Ok(()),
                        verification: Ok(()),
                        issuer_report: box IssuerReport::Root
                    }))
                })
            }
        );

        Ok(())
    }

    fn read_testdata(file: &str) -> String {
        fs::read_to_string(data_path(format!("oak_attestation_gcp/testdata/{file}"))).unwrap()
    }
}
