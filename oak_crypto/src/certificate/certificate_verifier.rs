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

use anyhow::{anyhow, Context};
use oak_proto_rust::oak::crypto::v1::{
    Certificate, CertificatePayload, SubjectPublicKeyInfo, Validity,
};
use prost::Message;

use crate::{certificate::utils::to_milliseconds_since_epoch, verifier::Verifier};

#[derive(Clone)]
pub struct CertificateVerifier<V: Verifier> {
    pub signature_verifier: V,
}

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
        Self::verify_subject_public_key_info(
            subject_public_key,
            purpose_id,
            subject_public_key_info,
        )
        .context("couldn't verify certificate payload")?;

        // Verify certificate validity.
        let validity = payload.validity.context("empty validity field")?;
        Self::verify_validity(milliseconds_since_epoch, &validity)
            .context("couldn't verify certificate validity")?;

        Ok(())
    }

    fn verify_subject_public_key_info(
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

    fn verify_validity(milliseconds_since_epoch: i64, validity: &Validity) -> anyhow::Result<()> {
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

        // TODO: b/417198320: - Increase the validity window verification according to a
        // time skew parameter. TODO: b/417198320: - Print timestamps as part of
        // the error.
        anyhow::ensure!(
            milliseconds_since_epoch >= not_before_milliseconds,
            "certificate validity period hasn't started yet",
        );
        anyhow::ensure!(milliseconds_since_epoch <= not_after_milliseconds, "certificate expired",);

        Ok(())
    }
}
