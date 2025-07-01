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

use base64::{engine::general_purpose::STANDARD, Engine};
use jwt::{Token, Unverified, Verified, VerifyWithKey};
use oak_time::Instant;
use serde_json::Value;
use x509_cert::{der::Decode, Certificate};
use x509_verify::VerifyingKey;

use crate::jwt::{algorithm::CertificateAlgorithm, Header};

pub const CONFIDENTIAL_SPACE_ROOT_CERT_PEM: &str =
    include_str!("../data/confidential_space_root.pem");

#[derive(thiserror::Error, Debug)]
pub enum AttestationVerificationError {
    #[error("Failed to verify JWT: {0}")]
    JWTError(#[from] jwt::Error),
    #[error("Invalid format parsing field {0}: {1}")]
    InvalidFormat(&'static str, &'static str),
    #[error("Failed to decode x5c: {0}")]
    X5CDecodeError(#[from] serde_json::Error),
    #[error("Invalid format parsing x5c: {0}")]
    X5CFormatError(&'static str),
    #[error("Failed to verify certificate: {0}")]
    X509VerificationError(x509_verify::Error),
    #[error("Failed to decode base64: {0}")]
    X509Base64DecodeError(#[from] base64::DecodeError),
    #[error("Failed to decode der: {0}")]
    X509DerDecodeError(x509_cert::der::Error),
    #[error("Unsupported signature algorithm")]
    UnsupportedSignatureAlgorithm,
    #[error("Certificate validity not_before: {not_before:?} > {current_time:?}")]
    X509ValidityNotBefore { not_before: Instant, current_time: Instant },
    #[error("Certificate validity not_after: {not_after:?} > {current_time:?}")]
    X509ValidityNotAfter { not_after: Instant, current_time: Instant },
    #[error("Token validity nbf: {nbf:?} > {current_time:?}")]
    JWTValidityNotBefore { nbf: Instant, current_time: Instant },
    #[error("Token validity exp: {exp:?} < {current_time:?}")]
    JWTValidityExpiration { exp: Instant, current_time: Instant },
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
    token: Token<Header, Value, Unverified>,
    root: &Certificate,
    current_time: &oak_time::Instant,
) -> Result<Token<Header, Value, Verified>, AttestationVerificationError> {
    // Verify the validity of the root certificate.
    verify_certificate_validity(root, current_time)?;

    let header = token.header();

    // Collect the x509 chain from base64 DER strings.
    let chain: Vec<Certificate> = (header.x509_chain.iter())
        .map(|base64_der| {
            let der = STANDARD.decode(base64_der)?;
            let certificate = Certificate::from_der(&der)?;
            Ok(certificate)
        })
        .collect::<Result<_, AttestationVerificationError>>()?;

    let mut issuer: &Certificate = root;
    for subject in chain.iter().rev() {
        verify_certificate_validity(issuer, current_time)?;
        VerifyingKey::try_from(issuer).and_then(|key| key.verify(subject))?;
        issuer = subject;
    }

    let key = CertificateAlgorithm::rs256(issuer)?;

    let verified = token.verify_with_key(&key)?;

    verify_token_validity(&verified, current_time)?;

    Ok(verified)
}

fn verify_certificate_validity(
    certificate: &Certificate,
    current_time: &oak_time::Instant,
) -> Result<(), AttestationVerificationError> {
    use oak_time::UNIX_EPOCH;

    let not_before =
        UNIX_EPOCH + certificate.tbs_certificate.validity.not_before.to_unix_duration();
    let not_after = UNIX_EPOCH + certificate.tbs_certificate.validity.not_after.to_unix_duration();

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

fn verify_token_validity(
    token: &Token<Header, Value, Verified>,
    current_time: &oak_time::Instant,
) -> Result<(), AttestationVerificationError> {
    let claims = token.claims();

    let token_not_after = match &claims["exp"] {
        Value::Number(exp) => {
            let unix_seconds = exp
                .as_i64()
                .ok_or(AttestationVerificationError::InvalidFormat("exp", "expected a number"))?;
            oak_time::Instant::from_unix_seconds(unix_seconds)
        }
        _ => return Err(AttestationVerificationError::InvalidFormat("exp", "expected a number")),
    };
    let token_not_before = match &claims["nbf"] {
        Value::Number(exp) => {
            let unix_seconds = exp
                .as_i64()
                .ok_or(AttestationVerificationError::InvalidFormat("nbf", "expected a number"))?;
            oak_time::Instant::from_unix_seconds(unix_seconds)
        }
        _ => return Err(AttestationVerificationError::InvalidFormat("exp", "expected a number")),
    };

    if &token_not_before > current_time {
        Err(AttestationVerificationError::JWTValidityNotBefore {
            nbf: token_not_before,
            current_time: *current_time,
        })
    } else if current_time > &token_not_after {
        Err(AttestationVerificationError::JWTValidityExpiration {
            exp: token_not_after,
            current_time: *current_time,
        })
    } else {
        Ok(())
    }
}
