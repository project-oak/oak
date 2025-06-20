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

use core::time::Duration;

use anyhow::{anyhow, Context};
use oak_proto_rust::oak::crypto::v1::{
    Certificate, CertificatePayload, SubjectPublicKeyInfo, Validity,
};
use oak_time::Instant;
use prost::{DecodeError, Message};

use crate::verifier::Verifier;

#[derive(Debug)]
pub struct CertificateVerificationReport {
    pub signature: SignatureReport,
    pub serialized_payload: PayloadDeserializationReport,
}

#[derive(Debug)]
pub enum SignatureReport {
    Missing,
    VerificationFailed(anyhow::Error),
    VerificationSucceeded,
}

#[derive(Debug)]
pub enum PayloadDeserializationReport {
    Failed(DecodeError),
    Succeeded { subject_public_key: SubjectPublicKeyReport, validity: ValidityPeriodReport },
}

#[derive(Debug)]
pub enum SubjectPublicKeyReport {
    Missing,
    Present { public_key_match: bool, purpose_id_match: bool },
}

#[derive(Debug)]
pub enum ValidityPeriodReport {
    Missing,
    Present {
        validity_period_is_positive: bool,
        validity_period_within_limit: bool,
        validity_period_started_on_or_before_timestamp: bool,
        validity_period_ended_at_or_after_timestamp: bool,
    },
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
    /// `validity_limit`. This only checks the validity provided by the
    /// certificate itself, i.e. doesn't consider the `allowed_clock_skew`.
    validity_limit: Option<Duration>,
}

impl<V: Verifier> CertificateVerifier<V> {
    /// Creates a new instance of [`CertificateVerifier`].
    pub fn new(signature_verifier: V) -> Self {
        Self { signature_verifier, allowed_clock_skew: Duration::default(), validity_limit: None }
    }

    /// Sets acceptable time period before the certificate validity starts and
    /// after it ends in order to account for devices with skewed clocks.
    pub fn set_allowed_clock_skew(&mut self, allowed_clock_skew: Duration) {
        self.allowed_clock_skew = allowed_clock_skew;
    }

    /// Sets maximum accepted certificate validity duration.
    pub fn set_validity_limit(&mut self, validity_limit: Duration) {
        self.validity_limit = Some(validity_limit);
    }
}

// TODO: b/407715638 - Use [`core::time`] instead of `i64` milliseconds.
/// Verifies the validity of the [`Certificate`] proto, which includes:
/// - Verifying its validity: check that `milliseconds_since_epoch` falls
///   withing the period defined by [`Validity`].
/// - Check that the payload contains expected [`subject_public_key`] and
///   [`purpose_id`].
impl<V: Verifier> CertificateVerifier<V> {
    pub fn verify(
        &self,
        subject_public_key: &[u8],
        purpose_id: &[u8],
        milliseconds_since_epoch: i64,
        certificate: &Certificate,
    ) -> anyhow::Result<()> {
        // Verify that certificate payload is signed correctly.
        let signature = certificate
            .signature_info
            .as_ref()
            .context("empty signature_info field")?
            .signature
            .as_ref();
        self.signature_verifier
            .verify(&certificate.serialized_payload, signature)
            .context("couldn't verify certificate signature")?;

        // Deserialize certificate payload.
        let payload = CertificatePayload::decode(certificate.serialized_payload.as_ref()).map_err(
            |error| anyhow!("couldn't deserialize certificate payload proto: {:?}", error),
        )?;

        // Verify public key info.
        let subject_public_key_info = payload
            .subject_public_key_info
            .as_ref()
            .context("empty subject_public_key_info field")?;
        self.verify_subject_public_key_info(
            subject_public_key,
            purpose_id,
            subject_public_key_info,
        )
        .context("couldn't verify certificate payload")?;

        // Verify certificate validity.
        let current_time = Instant::from_unix_millis(milliseconds_since_epoch);
        let validity = payload.validity.context("empty validity field")?;
        self.verify_validity(current_time, &validity)
            .context("couldn't verify certificate validity")?;

        Ok(())
    }

    pub fn report(
        &self,
        subject_public_key: &[u8],
        purpose_id: &[u8],
        milliseconds_since_epoch: i64,
        certificate: &Certificate,
    ) -> CertificateVerificationReport {
        // Verify that certificate payload is signed correctly.
        let signature_report = match certificate.signature_info.as_ref() {
            None => SignatureReport::Missing,
            Some(signature_info) => match self
                .signature_verifier
                .verify(&certificate.serialized_payload, signature_info.signature.as_ref())
            {
                Ok(_) => SignatureReport::VerificationSucceeded,
                Err(err) => SignatureReport::VerificationFailed(err),
            },
        };

        // Deserialize certificate payload.
        let payload_deserialization_report =
            match CertificatePayload::decode(certificate.serialized_payload.as_ref()) {
                Err(err) => PayloadDeserializationReport::Failed(err),
                Ok(payload) => PayloadDeserializationReport::Succeeded {
                    subject_public_key: match payload.subject_public_key_info.as_ref() {
                        None => SubjectPublicKeyReport::Missing,
                        Some(subject_public_key_info) => {
                            let certificate_payload_subject_public_key =
                                &subject_public_key_info.public_key;
                            let certificate_payload_purpose_id =
                                &subject_public_key_info.purpose_id;
                            SubjectPublicKeyReport::Present {
                                public_key_match: certificate_payload_subject_public_key
                                    == subject_public_key,
                                purpose_id_match: certificate_payload_purpose_id == purpose_id,
                            }
                        }
                    },
                    validity: match payload.validity {
                        None => ValidityPeriodReport::Missing,
                        Some(validity) => self.report_validity(
                            Instant::from_unix_millis(milliseconds_since_epoch),
                            &validity,
                        ),
                    },
                },
            };

        CertificateVerificationReport {
            signature: signature_report,
            serialized_payload: payload_deserialization_report,
        }
    }

    fn verify_subject_public_key_info(
        &self,
        expected_subject_public_key: &[u8],
        expected_purpose_id: &[u8],
        subject_public_key_info: &SubjectPublicKeyInfo,
    ) -> anyhow::Result<()> {
        let subject_public_key = &subject_public_key_info.public_key;
        let purpose_id = &subject_public_key_info.purpose_id;
        anyhow::ensure!(
            subject_public_key == expected_subject_public_key,
            "unexpected subject public key {subject_public_key:?}, expected {expected_subject_public_key:?}",
        );
        anyhow::ensure!(
            purpose_id == expected_purpose_id,
            "unexpected purpose ID {purpose_id:?}, expected {expected_purpose_id:?}",
        );
        Ok(())
    }

    /// Verifies that the certificate is valid at
    /// `current_time_milliseconds_since_epoch`. Verification is done by
    /// checking that `current_time_milliseconds_since_epoch` value is
    /// between [`Validity::not_before`] and [`Validity::not_after`]
    /// (inclusive).
    ///
    /// Also, if [`::allowed_clock_skew`] is not zero, then it's subtracted from
    /// the [`Validity::not_before`] and added to the [`Validity::not_after`]
    /// before verification to account for devices with skewed clocks.
    // TODO: b/429956843 - consolidate Validity verification.
    fn verify_validity(&self, current_time: Instant, validity: &Validity) -> anyhow::Result<()> {
        let not_before: Instant =
            validity.not_before.as_ref().context("Validity.not_before field is empty")?.into();
        let not_after: Instant =
            validity.not_after.as_ref().context("Validity.not_after field is empty")?.into();

        anyhow::ensure!(
            not_before < not_after,
            "not_before timestamp ({:?}) is not strictly earlier than not_after timestamp ({:?})",
            not_before,
            not_after,
        );

        // Discard certificates with validity duration longer than
        // [`CertificateVerifier::validity_limit`], if this value is not `None`.
        if let Some(validity_limit) = self.validity_limit {
            let validity_duration = not_after - not_before;
            anyhow::ensure!(
                validity_duration <= validity_limit,
                "certificate validity duration ({:?}) exceeds the maximum allowed validity duration ({:?})",
                validity_duration, self.validity_limit,
            )
        }

        // Account for skewed clock if [`CertificateVerifier::allowed_clock_skew`] is
        // non-zero.
        let skewed_not_before = not_before - self.allowed_clock_skew;
        let skewed_not_after = not_after + self.allowed_clock_skew;

        anyhow::ensure!(
            current_time >= skewed_not_before,
            "certificate validity period ({:?}) hasn't started yet (current time is {:?})",
            skewed_not_before,
            current_time,
        );
        anyhow::ensure!(
            current_time <= skewed_not_after,
            "certificate expired ({:?}) (current time is {:?})",
            skewed_not_after,
            current_time,
        );

        Ok(())
    }

    // TODO: b/429956843 - consolidate Validity verification.
    fn report_validity(&self, current_time: Instant, validity: &Validity) -> ValidityPeriodReport {
        let not_before: Instant = match validity.not_before.as_ref() {
            None => return ValidityPeriodReport::Missing,
            Some(not_before) => not_before.into(),
        };
        let not_after: Instant = match validity.not_after.as_ref() {
            None => return ValidityPeriodReport::Missing,
            Some(not_after) => not_after.into(),
        };
        let skewed_not_before = not_before - self.allowed_clock_skew;
        let skewed_not_after = not_after + self.allowed_clock_skew;
        ValidityPeriodReport::Present {
            validity_period_is_positive: not_before < not_after,
            validity_period_within_limit: if let Some(validity_limit) = self.validity_limit {
                let validity_duration = not_after - not_before;
                validity_duration <= validity_limit
            } else {
                true
            },
            validity_period_started_on_or_before_timestamp: current_time >= skewed_not_before,
            validity_period_ended_at_or_after_timestamp: current_time <= skewed_not_after,
        }
    }
}
