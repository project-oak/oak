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

use jwt::{AlgorithmType, algorithm::VerifyingAlgorithm};
use x509_cert::Certificate;
use x509_verify::{Signature, VerifyInfo, VerifyingKey};

/// An implementation of [`VerifyingAlgorithm`] to verify the signature of a JWT
/// that uses an X509 certificate to verify the signature  of a JWT token.
pub(crate) struct CertificateAlgorithm {
    verifying_key: VerifyingKey,
    /// The algorithm used to sign the JWT. [`AlgorithmIdentifier`] is not
    /// const-friendly because of the `parameters` field, so we have to use
    /// a struct variable to hold it.
    algorithm: x509_cert::spki::AlgorithmIdentifierOwned,
    /// The algorithm type used to sign the JWT. This should match the
    /// `algorithm` field above.
    algorithm_type: AlgorithmType,
}

impl CertificateAlgorithm {
    pub(crate) fn rs256(certificate: &Certificate) -> Result<Self, x509_verify::Error> {
        let algorithm = x509_cert::spki::AlgorithmIdentifierOwned {
            oid: const_oid::db::rfc5912::SHA_256_WITH_RSA_ENCRYPTION,
            parameters: Some(x509_cert::der::Any::null()),
        };
        // TODO: b/426463266 - Validate that the certificate public key algorithm is
        // compatible with the the signature algorithm (e.g. RSA key is
        // compatible with SHA_256_WITH_RSA signature algorithm).
        let verifying_key = VerifyingKey::try_from(certificate)?;
        Ok(Self { verifying_key, algorithm, algorithm_type: AlgorithmType::Rs256 })
    }
}

impl VerifyingAlgorithm for CertificateAlgorithm {
    fn algorithm_type(&self) -> AlgorithmType {
        self.algorithm_type
    }

    /// Verifies the signature of a JWT token.
    ///
    /// Parameters:
    ///
    /// * `header_base64`: The header of the token, as a url-safe base64 encoded
    ///   string without padding.
    /// * `claims_base64`: The claims payload of the token, as a url-safe base64
    ///   encoded string without padding.
    /// * `signature`: The signature of the token, already decoded into binary
    ///   from its orignal base64 representation.
    fn verify_bytes(
        &self,
        header_base64: &str,
        claims_base64: &str,
        signature: &[u8],
    ) -> Result<bool, jwt::error::Error> {
        // The Message struct in x509_verify crate only supports one-shot strs,
        // so we need to concatenate the header and claim to restore them to
        // the original signature format for verification.
        // https://datatracker.ietf.org/doc/html/rfc7515#section-5.1
        let signed_data = format!("{header_base64}.{claims_base64}");
        let info = VerifyInfo::new(
            signed_data.as_bytes().into(),
            Signature::new(&self.algorithm, signature),
        );
        self.verifying_key.verify(&info).map_err(|_| jwt::error::Error::InvalidSignature)?;
        Ok(true)
    }
}
