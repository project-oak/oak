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

#![feature(assert_matches)]
#![feature(box_patterns)]
#![feature(try_blocks)]

extern crate alloc;

pub mod attestation;
pub mod jwt;
pub mod policy;
pub mod verification;

#[cfg(test)]
mod tests {
    use core::assert_matches::assert_matches;
    use std::fs;

    use googletest::prelude::*;
    use jwt::{Token, Unverified};
    use oak_file_utils::data_path;
    use oak_time::{make_instant, Duration, Instant};
    use serde_json::Value;
    use x509_cert::{der::DecodePem, Certificate};

    use crate::{
        jwt::Header,
        verification::{
            report_attestation_token, verify_attestation_token, AttestationTokenVerificationReport,
            AttestationVerificationError, CertificateReport, IssuerReport,
        },
    };

    // The time has been set inside the validity interval of the test token.
    fn current_time() -> Instant {
        make_instant!("2025-06-23T15:00:00Z")
    }

    #[test]
    fn validate_token_ok() -> Result<()> {
        let token_str = read_testdata("valid.jwt");
        let root = Certificate::from_pem(read_testdata("root.crt"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Value, Unverified> =
            Token::parse_unverified(&token_str)?;

        verify_attestation_token(unverified_token, &root, &current_time())?;

        Ok(())
    }

    #[test]
    fn report_token_ok() -> Result<()> {
        let token_str = read_testdata("valid.jwt");
        let root = Certificate::from_pem(read_testdata("root.crt"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Value, Unverified> =
            Token::parse_unverified(&token_str)?;

        assert_matches!(
            report_attestation_token(unverified_token, &root, &current_time()),
            AttestationTokenVerificationReport{
                validity: Ok(()),
                verification: Ok(_),
                issuer_report: Ok(CertificateReport{
                    validity: Ok(()),
                    verification: Ok(()),
                    issuer_report: box IssuerReport::OtherCertificate(
                        Ok(CertificateReport{
                            validity: Ok(()),
                            verification: Ok(()),
                            issuer_report: box IssuerReport::OtherCertificate(
                                Ok(CertificateReport{
                                    validity: Ok(()),
                                    verification: Ok(()),
                                    issuer_report: box IssuerReport::OtherCertificate(
                                        Ok(CertificateReport{
                                            validity: Ok(()),
                                            verification: Ok(()),
                                            issuer_report: box IssuerReport::SelfSigned
                                        })
                                    )
                                })
                            )
                        })
                    )
                })
            }
        );

        Ok(())
    }

    #[test]
    fn validate_token_invalid_signature() -> Result<()> {
        let token_str = read_testdata("invalid_signature.jwt");
        let root = Certificate::from_pem(read_testdata("root.crt"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Value, Unverified> =
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
        let token_str = read_testdata("invalid_signature.jwt");
        let root = Certificate::from_pem(read_testdata("root.crt"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Value, Unverified> =
            Token::parse_unverified(&token_str)?;

        assert_matches!(
            report_attestation_token(unverified_token, &root, &current_time()),
            AttestationTokenVerificationReport{
                validity: Ok(()),
                verification: Err(AttestationVerificationError::JWTError(jwt::Error::InvalidSignature)),
                issuer_report: Ok(CertificateReport{
                    validity: Ok(()),
                    verification: Ok(()),
                    issuer_report: box IssuerReport::OtherCertificate(
                        Ok(CertificateReport{
                            validity: Ok(()),
                            verification: Ok(()),
                            issuer_report: box IssuerReport::OtherCertificate(
                                Ok(CertificateReport{
                                    validity: Ok(()),
                                    verification: Ok(()),
                                    issuer_report: box IssuerReport::OtherCertificate(
                                        Ok(CertificateReport{
                                            validity: Ok(()),
                                            verification: Ok(()),
                                            issuer_report: box IssuerReport::SelfSigned
                                        })
                                    )
                                })
                            )
                        })
                    )
                })
            }
        );

        Ok(())
    }

    #[test]
    fn validate_token_expired_token() -> Result<()> {
        let token_str = read_testdata("valid.jwt");
        let root = Certificate::from_pem(read_testdata("root.crt"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Value, Unverified> =
            Token::parse_unverified(&token_str)?;

        // Advance the clock by about 1h
        let expired_current_time = current_time() + Duration::from_seconds(3600);

        assert_matches!(
            unsafe {
                verify_attestation_token(unverified_token, &root, &expired_current_time)
                    .unwrap_err_unchecked()
            },
            AttestationVerificationError::JWTValidityExpiration { .. }
        );

        Ok(())
    }

    #[test]
    fn report_token_expired_token() -> Result<()> {
        let token_str = read_testdata("valid.jwt");
        let root = Certificate::from_pem(read_testdata("root.crt"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Value, Unverified> =
            Token::parse_unverified(&token_str)?;

        // Advance the clock by about 1h
        let expired_current_time = current_time() + Duration::from_seconds(3600);

        assert_matches!(
            report_attestation_token(unverified_token, &root, &expired_current_time),
            AttestationTokenVerificationReport{
                validity: Err(AttestationVerificationError::JWTValidityExpiration { .. }),
                verification: Ok(_),
                issuer_report: Ok(CertificateReport{
                    validity: Ok(()),
                    verification: Ok(()),
                    issuer_report: box IssuerReport::OtherCertificate(
                        Ok(CertificateReport{
                            validity: Ok(()),
                            verification: Ok(()),
                            issuer_report: box IssuerReport::OtherCertificate(
                                Ok(CertificateReport{
                                    validity: Ok(()),
                                    verification: Ok(()),
                                    issuer_report: box IssuerReport::OtherCertificate(
                                        Ok(CertificateReport{
                                            validity: Ok(()),
                                            verification: Ok(()),
                                            issuer_report: box IssuerReport::SelfSigned
                                        })
                                    )
                                })
                            )
                        })
                    )
                })
            }
        );

        Ok(())
    }

    #[test]
    fn validate_token_expired_cert() -> Result<()> {
        let token_str = read_testdata("valid.jwt");
        let root = Certificate::from_pem(read_testdata("root.crt"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Value, Unverified> =
            Token::parse_unverified(&token_str)?;

        // Advance the clock by about 100 years
        let expired_current_time = current_time() + Duration::from_seconds(100 * 365 * 24 * 3600);

        assert_matches!(
            unsafe {
                verify_attestation_token(unverified_token, &root, &expired_current_time)
                    .unwrap_err_unchecked()
            },
            AttestationVerificationError::JWTValidityExpiration { .. }
        );

        Ok(())
    }

    #[test]
    fn report_token_expired_cert() -> Result<()> {
        let token_str = read_testdata("valid.jwt");
        let root = Certificate::from_pem(read_testdata("root.crt"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Value, Unverified> =
            Token::parse_unverified(&token_str)?;

        // Advance the clock by about 100 years
        let expired_current_time = current_time() + Duration::from_seconds(100 * 365 * 24 * 3600);

        assert_matches!(
            report_attestation_token(unverified_token, &root, &expired_current_time),
            AttestationTokenVerificationReport{
                validity: Err(AttestationVerificationError::JWTValidityExpiration { .. }),
                verification: Ok(_),
                issuer_report: Ok(CertificateReport{
                    validity: Err(AttestationVerificationError::X509ValidityNotAfter { .. }),
                    verification: Ok(()),
                    issuer_report: box IssuerReport::OtherCertificate(
                        Ok(CertificateReport{
                            validity: Err(AttestationVerificationError::X509ValidityNotAfter { .. }),
                            verification: Ok(()),
                            issuer_report: box IssuerReport::OtherCertificate(
                                Ok(CertificateReport{
                                    validity: Err(AttestationVerificationError::X509ValidityNotAfter { .. }),
                                    verification: Ok(()),
                                    issuer_report: box IssuerReport::OtherCertificate(
                                        Ok(CertificateReport{
                                            validity: Err(AttestationVerificationError::X509ValidityNotAfter { .. }),
                                            verification: Ok(()),
                                            issuer_report: box IssuerReport::SelfSigned
                                        })
                                    )
                                })
                            )
                        })
                    )
                })
            }
        );

        Ok(())
    }

    fn read_testdata(file: &str) -> String {
        fs::read_to_string(data_path(format!("oak_attestation_gcp/testdata/{file}"))).unwrap()
    }
}
