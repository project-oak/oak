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

use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

use anyhow::Context;
use oak_attestation_verification_types::policy::Policy;
use oak_crypto::{certificate::certificate_verifier::CertificateVerifier, verifier::Verifier};
use oak_proto_rust::oak::{
    attestation::v1::{
        session_binding_public_key_endorsement, EventAttestationResults,
        SessionBindingPublicKeyData, SessionBindingPublicKeyEndorsement,
    },
    Variant,
};

use crate::{policy::SESSION_BINDING_PUBLIC_KEY_ID, util::decode_event_proto};

pub struct SessionBindingPublicKeyPolicy<V: Verifier> {
    certificate_verifier: CertificateVerifier<V>,
}

impl<V: Verifier> SessionBindingPublicKeyPolicy<V> {
    pub fn new(certificate_verifier: CertificateVerifier<V>) -> Self {
        Self { certificate_verifier }
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
        _milliseconds_since_epoch: i64,
    ) -> anyhow::Result<EventAttestationResults> {
        let event = decode_event_proto::<SessionBindingPublicKeyData>(
            "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData",
            encoded_event,
        )?;
        let endorsement: Option<SessionBindingPublicKeyEndorsement> =
            encoded_endorsement.try_into().map_err(anyhow::Error::msg)?;

        match &endorsement
            .context("endorsment for session binding public key is not present")?
            .r#type
        {
            Some(session_binding_public_key_endorsement::Type::TinkEndorsement(
                tink_endorsement,
            )) => {
                self.certificate_verifier
                    .signature_verifier
                    .verify(&event.session_binding_public_key, &tink_endorsement.signature)
                    .context("couldn't verify tink endorsement")?;
            }
            Some(
                session_binding_public_key_endorsement::Type::CertificateAuthorityEndorsement(
                    _value,
                ),
            ) => {
                anyhow::bail!("CertificateAuthorityEndorsment not supported")
            }
            None => anyhow::bail!("SessionBindingPublicKeyEndorsement is empty"),
        };

        let mut artifacts = BTreeMap::<String, Vec<u8>>::new();
        if !event.session_binding_public_key.is_empty() {
            artifacts.insert(
                SESSION_BINDING_PUBLIC_KEY_ID.to_string(),
                event.session_binding_public_key.to_vec(),
            );
        } else {
            anyhow::bail!("session binding public key not found")
        }

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults { artifacts })
    }
}
