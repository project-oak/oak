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

use alloc::{collections::BTreeMap, string::ToString};

use anyhow::Context;
use oak_attestation_verification_types::policy::Policy;
use oak_crypto::{
    certificate::certificate_verifier::{CertificateVerificationReport, CertificateVerifier},
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

use crate::{policy::SESSION_BINDING_PUBLIC_KEY_ID, util::decode_event_proto};

#[derive(Debug)]
pub struct SessionBindingPublicKeyVerificationReport {
    pub event: EventDeserializationReport,
    pub endorsement: EndorsementReport,
}

#[derive(Debug)]
pub enum EventDeserializationReport {
    Failed(anyhow::Error),
    Succeeded { has_session_binding_public_key: bool },
}

#[derive(Debug)]
pub enum EndorsementReport {
    DeserializationFailed(&'static str),
    MissingCertificateAuthorityEndorsement,
    MissingCertificate,
    InvalidEvent,
    Checked(CertificateVerificationReport),
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
        encoded_event: &[u8],
        encoded_endorsement: &Variant,
        milliseconds_since_epoch: i64,
    ) -> SessionBindingPublicKeyVerificationReport {
        let event = decode_event_proto::<SessionBindingPublicKeyData>(
            "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData",
            encoded_event,
        );

        let session_binding_public_key;
        let event_report = match event {
            Err(err) => {
                session_binding_public_key = Option::None;
                EventDeserializationReport::Failed(err)
            }
            Ok(event) => {
                if !event.session_binding_public_key.is_empty() {
                    session_binding_public_key = Option::Some(event.session_binding_public_key);
                } else {
                    session_binding_public_key = Option::None;
                }
                EventDeserializationReport::Succeeded {
                    has_session_binding_public_key: session_binding_public_key.is_some(),
                }
            }
        };

        let endorsement_report =
            match <&Variant as TryInto<SessionBindingPublicKeyEndorsement>>::try_into(
                encoded_endorsement,
            ) {
                Err(err) => EndorsementReport::DeserializationFailed(err),
                Ok(endorsement) => match endorsement.ca_endorsement {
                    None => EndorsementReport::MissingCertificateAuthorityEndorsement,
                    Some(ca_endorsement) => match ca_endorsement.certificate {
                        None => EndorsementReport::MissingCertificate,
                        Some(certificate) => match session_binding_public_key {
                            None => EndorsementReport::InvalidEvent,
                            Some(session_binding_public_key) => {
                                EndorsementReport::Checked(self.certificate_verifier.report(
                                    &session_binding_public_key,
                                    &SESSION_BINDING_PUBLIC_KEY_PURPOSE_ID,
                                    milliseconds_since_epoch,
                                    &certificate,
                                ))
                            }
                        },
                    },
                },
            };

        SessionBindingPublicKeyVerificationReport {
            event: event_report,
            endorsement: endorsement_report,
        }
    }
}

// We have to use [`Policy<[u8]>`] instead of [`EventPolicy`], because
// Rust doesn't yet support implementing trait aliases.
// <https://github.com/rust-lang/rfcs/blob/master/text/1733-trait-alias.md>
impl<V: Verifier> Policy<[u8]> for SessionBindingPublicKeyPolicy<V> {
    fn verify(
        &self,
        encoded_event: &[u8],
        encoded_endorsement: &Variant,
        milliseconds_since_epoch: i64,
    ) -> anyhow::Result<EventAttestationResults> {
        let event = decode_event_proto::<SessionBindingPublicKeyData>(
            "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData",
            encoded_event,
        )?;
        if event.session_binding_public_key.is_empty() {
            anyhow::bail!("session binding public key not found")
        }

        let endorsement = <&Variant as TryInto<SessionBindingPublicKeyEndorsement>>::try_into(
            encoded_endorsement,
        )
        .map_err(anyhow::Error::msg)
        .context("certificate authority endorsement is not present")?;

        match endorsement.ca_endorsement {
            None => {
                anyhow::bail!("SessionBindingPublicKeyEndorsement.ca_endorsement field is empty")
            }
            Some(certificate_authority_endorsement) => {
                let certificate = certificate_authority_endorsement
                    .certificate
                    .as_ref()
                    .context("certificate is not present in the CertificateAuthorityEndorsement")?;
                self.certificate_verifier
                    .verify(
                        &event.session_binding_public_key,
                        &SESSION_BINDING_PUBLIC_KEY_PURPOSE_ID,
                        milliseconds_since_epoch,
                        certificate,
                    )
                    .context("couldn't verify certificate for session binding public key")?;
            }
        }

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults {
            artifacts: BTreeMap::from([(
                SESSION_BINDING_PUBLIC_KEY_ID.to_string(),
                event.session_binding_public_key.to_vec(),
            )]),
        })
    }
}
