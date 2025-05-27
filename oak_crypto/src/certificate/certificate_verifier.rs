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
use prost::Message;

use crate::{certificate::utils::to_milliseconds_since_epoch, verifier::Verifier};

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
}

impl<V: Verifier> CertificateVerifier<V> {
    /// Creates a new instance of [`CertificateVerifier`].
    pub fn new(signature_verifier: V) -> Self {
        Self { signature_verifier, allowed_clock_skew: Duration::default() }
    }

    /// Adds acceptable time period before the certificate validity starts and
    /// after it ends in order to account for devices with skewed clocks.
    pub fn set_allowed_clock_skew(&mut self, allowed_clock_skew: Duration) {
        self.allowed_clock_skew = allowed_clock_skew;
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
        let validity = payload.validity.context("empty validity field")?;
        self.verify_validity(milliseconds_since_epoch, &validity)
            .context("couldn't verify certificate validity")?;

        Ok(())
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
    fn verify_validity(
        &self,
        current_time_milliseconds_since_epoch: i64,
        validity: &Validity,
    ) -> anyhow::Result<()> {
        let not_before_milliseconds = to_milliseconds_since_epoch(
            validity.not_before.as_ref().context("Validity.not_before field is empty")?,
        );
        let not_after_milliseconds = to_milliseconds_since_epoch(
            validity.not_after.as_ref().context("Validity.not_after field is empty")?,
        );
        anyhow::ensure!(
            not_before_milliseconds < not_after_milliseconds,
            "not_before timestamp is not strictly earlier than not_after timestamp",
        );
        let skewed_not_before_milliseconds =
            not_before_milliseconds - (self.allowed_clock_skew.as_millis() as i64);
        let skewed_not_after_milliseconds =
            not_after_milliseconds + (self.allowed_clock_skew.as_millis() as i64);

        // TODO: b/414973682: - Print timestamps as part of the error.
        anyhow::ensure!(
            current_time_milliseconds_since_epoch >= skewed_not_before_milliseconds,
            "certificate validity period hasn't started yet",
        );
        anyhow::ensure!(
            current_time_milliseconds_since_epoch <= skewed_not_after_milliseconds,
            "certificate expired"
        );

        Ok(())
    }
}
