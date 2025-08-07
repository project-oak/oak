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

use alloc::vec::Vec;

use oak_attestation_verification_types::policy::Policy;
use oak_crypto::{
    certificate::certificate_verifier::{
        CertificateVerificationError, CertificateVerificationReport, CertificateVerifier,
    },
    verifier::Verifier,
};
use oak_proto_rust::{
    certificate::SESSION_BINDING_PUBLIC_KEY_PURPOSE_ID,
    oak::{
        attestation::v1::{
            EventAttestationResults, SessionBindingPublicKeyData,
            SessionBindingPublicKeyEndorsement,
        },
        Variant,
    },
};
use oak_time::Instant;

use crate::{results::set_session_binding_public_key, util::decode_event_proto};

#[derive(Debug)]
pub struct SessionBindingPublicKeyVerificationReport {
    pub session_binding_public_key: Vec<u8>,
    pub endorsement: Result<CertificateVerificationReport, CertificateVerificationError>,
}

impl SessionBindingPublicKeyVerificationReport {
    fn into_session_binding_public_key(
        self,
    ) -> Result<Vec<u8>, SessionBindingPublicKeyVerificationError> {
        match self {
            SessionBindingPublicKeyVerificationReport {
                session_binding_public_key,
                endorsement: Ok(certificate_verification_report),
            } => Ok(certificate_verification_report
                .into_checked()
                .map(|_| session_binding_public_key)?),
            SessionBindingPublicKeyVerificationReport {
                session_binding_public_key: _,
                endorsement: Err(err),
            } => Err(SessionBindingPublicKeyVerificationError::CertificateVerificationError(err)),
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum SessionBindingPublicKeyVerificationError {
    #[error("Missing field: {0}")]
    MissingField(&'static str),
    #[error("Failed to decode proto: {0}")]
    ProtoDecodeError(#[from] anyhow::Error),
    #[error("Failed to decode Variant: {0}")]
    VariantDecodeError(&'static str),
    #[error("Certificate verification failed: {0}")]
    CertificateVerificationError(#[from] CertificateVerificationError),
}

pub struct SessionBindingPublicKeyPolicy<V: Verifier> {
    certificate_verifier: CertificateVerifier<V>,
}

impl<V: Verifier> SessionBindingPublicKeyPolicy<V> {
    pub fn new(certificate_verifier: CertificateVerifier<V>) -> Self {
        Self { certificate_verifier }
    }

    // This is a copy of verify() except that it returns a report of the results
    // of running as many verification checks as possible (i.e. no fail-fast).
    pub fn report(
        &self,
        current_time: Instant,
        encoded_event: &[u8],
        encoded_endorsement: &Variant,
    ) -> Result<SessionBindingPublicKeyVerificationReport, SessionBindingPublicKeyVerificationError>
    {
        let event = decode_event_proto::<SessionBindingPublicKeyData>(
            "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData",
            encoded_event,
        )?;
        if event.session_binding_public_key.is_empty() {
            return Err(SessionBindingPublicKeyVerificationError::MissingField(
                "SessionBindingPublicKeyData.session_binding_public_key",
            ));
        }

        let ca_endorsement = <&Variant as TryInto<SessionBindingPublicKeyEndorsement>>::try_into(
            encoded_endorsement,
        )
        .map_err(SessionBindingPublicKeyVerificationError::VariantDecodeError)?
        .ca_endorsement
        .ok_or(SessionBindingPublicKeyVerificationError::MissingField(
            "SessionBindingPublicKeyEndorsement.ca_endorsement",
        ))?;
        let certificate = ca_endorsement.certificate.as_ref().ok_or(
            SessionBindingPublicKeyVerificationError::MissingField(
                "CertificateAuthorityEndorsement.certificate",
            ),
        )?;

        Ok(SessionBindingPublicKeyVerificationReport {
            session_binding_public_key: event.session_binding_public_key.clone(),
            endorsement: self.certificate_verifier.report(
                current_time,
                &event.session_binding_public_key,
                &SESSION_BINDING_PUBLIC_KEY_PURPOSE_ID,
                certificate,
            ),
        })
    }
}

// We have to use [`Policy<[u8]>`] instead of [`EventPolicy`], because
// Rust doesn't yet support implementing trait aliases.
// <https://github.com/rust-lang/rfcs/blob/master/text/1733-trait-alias.md>
impl<V: Verifier> Policy<[u8]> for SessionBindingPublicKeyPolicy<V> {
    fn verify(
        &self,
        current_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let report = self.report(current_time, evidence, endorsement)?;
        let mut results = EventAttestationResults { ..Default::default() };
        set_session_binding_public_key(&mut results, &report.into_session_binding_public_key()?);
        Ok(results)
    }
}
