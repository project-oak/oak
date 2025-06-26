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

use alloc::{format, string::String};

use oak_proto_rust::oak::{
    crypto::v1::{Certificate, CertificatePayload, ProofOfFreshness, SubjectPublicKeyInfo},
    Validity,
};
use oak_time::{Duration, Instant};
use prost::{DecodeError, Message};

use crate::verifier::Verifier;

#[derive(thiserror::Error, Debug)]
pub enum CertificateVerificationError {
    #[error("Missing field: {0}")]
    MissingField(&'static str),
    #[error("Failed to decode proto: {0}")]
    ProtoDecodeError(DecodeError),
    #[error("Signature verification failed: {0}")]
    SignatureVerificationError(#[from] anyhow::Error),
    #[error("Subject public key mismatch; expected {expected} but got {actual}")]
    SubjectPublicKeyMismatch { expected: String, actual: String },
    #[error("Purpose ID mismatch; expected {expected} but got {actual}")]
    PurposeIdMismatch { expected: String, actual: String },
    #[error("Invalid certificate validity period; not_before {not_before} is after not_after {not_after}")]
    ValidityPeriodInvalid { not_before: Instant, not_after: Instant },
    #[error("Certificate validity period {period:?} exceeds the limit {limit:?}")]
    ValidityPeriodTooLong { period: Duration, limit: Duration },
    #[error(
        "Certificate validity period begins at (skewed) {skewed_not_before}, after {current_time}"
    )]
    ValidityPeriodNotYetStarted { skewed_not_before: Instant, current_time: Instant },
    #[error(
        "Certificate validity period ends at (skewed) {skewed_not_after}, before {current_time}"
    )]
    ValidityPeriodExpired { skewed_not_after: Instant, current_time: Instant },
    // TODO: b/424736845 - Remove this once proof of freshness is implemented.
    #[error("Proof of freshness verification is not implemented")]
    ProofOfFreshnessUnimplemented,
    #[error("Unknown error: {0}")]
    UnknownError(&'static str),
}

// Manual [From] implementation required because DecodeError is missing
// required traits (to be able to use `#[from]`) in no-std environments.
impl From<DecodeError> for CertificateVerificationError {
    fn from(e: DecodeError) -> CertificateVerificationError {
        CertificateVerificationError::ProtoDecodeError(e)
    }
}

#[derive(Debug)]
pub struct CertificateVerificationReport {
    pub validity: Result<(), CertificateVerificationError>,
    pub verification: Result<(), CertificateVerificationError>,
    pub freshness: Option<Result<(), CertificateVerificationError>>,
}

impl CertificateVerificationReport {
    pub fn into_checked(self) -> Result<(), CertificateVerificationError> {
        match self {
            CertificateVerificationReport {
                validity: Ok(()),
                verification: Ok(()),
                freshness: None,
            }
            | CertificateVerificationReport {
                validity: Ok(()),
                verification: Ok(()),
                freshness: Some(Ok(())),
            } => Ok(()),
            CertificateVerificationReport { validity, verification, freshness } => {
                validity?;
                verification?;
                if let Some(freshness_val) = freshness {
                    freshness_val?;
                }
                Err(CertificateVerificationError::UnknownError(
                    "CertificateVerificationReport verification failed",
                ))
            }
        }
    }
}

#[derive(Clone)]
pub enum ProofOfFreshnessVerification {
    Ignore,
    Verify,
}

/// Struct that verifies the validity of the [`Certificate`] proto, which
/// includes verifying its validity and that it contains expected fields.
/// It relies on the [`Verifier`] to verify that [`Certificate::signature_info`]
/// field correctly signs the [`Certificate::serialized_payload`], i.e. to
/// verify the raw signature.
#[derive(Clone)]
pub struct CertificateVerifier<V: Verifier> {
    pub signature_verifier: V,
    /// Acceptable time period that corresponds to the device clock skew. The
    /// default value is `0`, which means that there is no clock skew.
    allowed_clock_skew: Duration,
    /// Maximum accepted certificate validity duration.
    /// The default `None` value means that any certificate validity is
    /// accepted. If set, then the certificate verifier will only accept
    /// certificates with the validity duration less or equal than
    /// `max_validity_duration`. This only checks the validity provided by the
    /// certificate itself, i.e. doesn't consider the `allowed_clock_skew`.
    max_validity_duration: Option<Duration>,
    // Whether to verify the proof of freshness in the certificate.
    proof_of_freshness_verification: ProofOfFreshnessVerification,
}

impl<V: Verifier> CertificateVerifier<V> {
    /// Creates a new instance of [`CertificateVerifier`].
    pub fn new(signature_verifier: V) -> Self {
        Self {
            signature_verifier,
            allowed_clock_skew: Duration::default(),
            max_validity_duration: None,
            proof_of_freshness_verification: ProofOfFreshnessVerification::Ignore,
        }
    }

    /// Sets acceptable time period before the certificate validity starts and
    /// after it ends in order to account for devices with skewed clocks.
    pub fn set_allowed_clock_skew(&mut self, allowed_clock_skew: Duration) {
        self.allowed_clock_skew = allowed_clock_skew;
    }

    /// Sets maximum accepted certificate validity duration.
    pub fn set_max_validity_duration(&mut self, max_validity_duration: Duration) {
        self.max_validity_duration = Some(max_validity_duration);
    }

    /// Sets maximum accepted certificate validity duration.
    // TODO: b/419209669 - remove this once callers are migrated to
    // set_max_validity_duration().
    pub fn set_validity_limit(&mut self, max_validity_duration: Duration) {
        self.max_validity_duration = Some(max_validity_duration);
    }

    // Sets extra checks that the verifier can perform as part of the `verify`
    // function.
    pub fn set_proof_of_freshness_verification(
        &mut self,
        proof_of_freshness_verification: ProofOfFreshnessVerification,
    ) {
        self.proof_of_freshness_verification = proof_of_freshness_verification;
    }
}

/// Verifies the validity of the [`Certificate`] proto, which includes:
/// - Verifying its validity: check that `current_time` falls within the period
///   defined by [`Validity`].
/// - Check that the payload contains expected [`subject_public_key`] and
///   [`purpose_id`].
impl<V: Verifier> CertificateVerifier<V> {
    pub fn verify(
        &self,
        current_time: Instant,
        subject_public_key: &[u8],
        purpose_id: &[u8],
        certificate: &Certificate,
    ) -> Result<(), CertificateVerificationError> {
        self.report(current_time, subject_public_key, purpose_id, certificate)?.into_checked()
    }

    pub fn report(
        &self,
        current_time: Instant,
        subject_public_key: &[u8],
        purpose_id: &[u8],
        certificate: &Certificate,
    ) -> Result<CertificateVerificationReport, CertificateVerificationError> {
        let payload = CertificatePayload::decode(certificate.serialized_payload.as_ref())?;
        let subject_public_key_info = payload.subject_public_key_info.as_ref().ok_or(
            CertificateVerificationError::MissingField(
                "CertificatePayload.subject_public_key_info",
            ),
        )?;
        let validity = payload
            .validity
            .ok_or(CertificateVerificationError::MissingField("CertificatePayload.validity"))?;
        let proof_of_freshness_option = payload.proof_of_freshness;

        Ok(CertificateVerificationReport {
            validity: self.verify_validity(current_time, &validity),
            verification: try {
                let signature = certificate
                    .signature_info
                    .as_ref()
                    .ok_or(CertificateVerificationError::MissingField(
                        "Certificate.signature_info",
                    ))?
                    .signature
                    .as_ref();
                self.signature_verifier.verify(&certificate.serialized_payload, signature)?;
                self.verify_subject_public_key_info(
                    subject_public_key,
                    purpose_id,
                    subject_public_key_info,
                )?;
            },
            freshness: match self.proof_of_freshness_verification {
                ProofOfFreshnessVerification::Ignore => None,
                ProofOfFreshnessVerification::Verify => {
                    let proof_of_freshness = proof_of_freshness_option.ok_or(
                        CertificateVerificationError::MissingField(
                            "Certificate.proof_of_freshness",
                        ),
                    )?;
                    Some(self.verify_proof_of_freshness(proof_of_freshness))
                }
            },
        })
    }

    fn verify_subject_public_key_info(
        &self,
        expected_subject_public_key: &[u8],
        expected_purpose_id: &[u8],
        subject_public_key_info: &SubjectPublicKeyInfo,
    ) -> Result<(), CertificateVerificationError> {
        let subject_public_key = &subject_public_key_info.public_key;
        let purpose_id = &subject_public_key_info.purpose_id;
        if subject_public_key != expected_subject_public_key {
            return Err(CertificateVerificationError::SubjectPublicKeyMismatch {
                expected: format!("{expected_subject_public_key:?}"),
                actual: format!("{subject_public_key:?}"),
            });
        }
        if purpose_id != expected_purpose_id {
            return Err(CertificateVerificationError::PurposeIdMismatch {
                expected: format!("{expected_purpose_id:?}"),
                actual: format!("{purpose_id:?}"),
            });
        }
        Ok(())
    }

    /// Verifies that the certificate is valid at `current_time`.
    ///
    /// Also, if [`::allowed_clock_skew`] is not zero, then it's subtracted from
    /// the [`Validity::not_before`] and added to the [`Validity::not_after`]
    /// before verification to account for devices with skewed clocks.
    // TODO: b/429956843 - consolidate Validity verification.
    fn verify_validity(
        &self,
        current_time: Instant,
        validity: &Validity,
    ) -> Result<(), CertificateVerificationError> {
        let not_before: Instant = validity
            .not_before
            .as_ref()
            .ok_or(CertificateVerificationError::MissingField("Validity.not_before"))?
            .into();
        let not_after: Instant = validity
            .not_after
            .as_ref()
            .ok_or(CertificateVerificationError::MissingField("Validity.not_after"))?
            .into();

        if not_before > not_after {
            return Err(CertificateVerificationError::ValidityPeriodInvalid {
                not_before,
                not_after,
            });
        }

        // Discard certificates with validity duration longer than
        // [`CertificateVerifier::max_validity_duration`], if this value is not `None`.
        if let Some(max_validity_duration) = self.max_validity_duration {
            let validity_duration = not_after - not_before;
            if validity_duration > max_validity_duration {
                return Err(CertificateVerificationError::ValidityPeriodTooLong {
                    period: validity_duration,
                    limit: max_validity_duration,
                });
            }
        }

        // Account for skewed clock if [`CertificateVerifier::allowed_clock_skew`] is
        // non-zero.
        let skewed_not_before = not_before - self.allowed_clock_skew;
        let skewed_not_after = not_after + self.allowed_clock_skew;
        if current_time < skewed_not_before {
            return Err(CertificateVerificationError::ValidityPeriodNotYetStarted {
                skewed_not_before,
                current_time,
            });
        }
        if current_time > skewed_not_after {
            return Err(CertificateVerificationError::ValidityPeriodExpired {
                skewed_not_after,
                current_time,
            });
        }

        Ok(())
    }

    fn verify_proof_of_freshness(
        &self,
        _proof_of_freshness: ProofOfFreshness,
    ) -> Result<(), CertificateVerificationError> {
        // TODO: b/424736845 - Verify proof of freshness evidence.
        Err(CertificateVerificationError::ProofOfFreshnessUnimplemented)
    }
}
