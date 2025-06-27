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
use serde_json::Value;
use x509_cert::{der::Decode, Certificate};
use x509_verify::VerifyingKey;

use crate::{
    //der::{Base64DerError, FromBase64Der},
    jwt::{algorithm::CertificateAlgorithm, Header},
};

#[derive(thiserror::Error, Debug)]
pub enum AttestationVerificationError {
    #[error("Failed to verify JWT: {0}")]
    JWTError(#[from] jwt::Error),
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
    #[error("Reference root sha256 mismatch: {0}")]
    ReferenceRootSha256Mismatch(String),
    #[error("Unsupported signature algorithm")]
    UnsupportedSignatureAlgorithm,
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
/// TODO: b/426463266 - Check the x509 validity and token expiration.
pub fn verify_attestation_token(
    token: Token<Header, Value, Unverified>,
    root: &Certificate,
) -> Result<Token<Header, Value, Verified>, AttestationVerificationError> {
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
        VerifyingKey::try_from(issuer).and_then(|key| key.verify(subject))?;
        issuer = subject;
    }

    let key = CertificateAlgorithm::rs256(issuer)?;

    let verified = token.verify_with_key(&key)?;

    Ok(verified)
}
