//
// Copyright 2021 The Project Oak Authors
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

pub mod attested_session;
pub mod unattested_session;

use crate::{
    attestation::{
        attested_session::AttestedSession,
        unattested_session::{
            MutuallyUnattested, UnattestedPeer, UnattestedSelf, UnattestedSession,
        },
    },
    crypto::{get_sha256, AeadEncryptor, KeyNegotiator},
    proto::AttestationIdentity,
};
use anyhow::Context;

/// Remote attestation protocol implementation.
pub struct AttestationEngine<S> {
    /// Type of the remote attestation process.
    attestation_type: S,
    /// Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
    key_negotiator: KeyNegotiator,
}

impl<S> AttestationEngine<S>
where
    S: UnattestedSession,
{
    /// Returns an [`AttestationIdentity`] that contains a public key and possibly an attestation
    /// info (depending on `Self::attestation_type`).
    pub fn identity(&self) -> anyhow::Result<AttestationIdentity> {
        let public_key = self
            .key_negotiator
            .public_key()
            .context("Couldn't get public key")?;
        let public_key_hash = get_sha256(&public_key);
        let attestation_info = self.attestation_type.get_attestation_info(&public_key_hash);

        Ok(AttestationIdentity {
            public_key,
            attestation_info,
        })
    }

    /// Verifies remote attestation, negotiates a session key and creates an [`AttestedSession`].
    pub fn create_attested_session(
        self,
        peer_identity: &AttestationIdentity,
    ) -> anyhow::Result<AttestedSession> {
        self.attestation_type
            .verify_attestation(&peer_identity)
            .context("Couldn't verify peer attestation info")?;

        // Generate session key.
        let session_key = self
            .key_negotiator
            .derive_session_key(peer_identity.public_key.as_ref())
            .context("Couldn't derive session key")?;

        let encryptor = AeadEncryptor::new(session_key);
        Ok(AttestedSession::new(encryptor))
    }
}

impl AttestationEngine<UnattestedSelf> {
    pub fn create(tee_certificate: &[u8]) -> anyhow::Result<Self> {
        let key_negotiator = KeyNegotiator::create().context("Couldn't create key negotiator")?;
        Ok(Self {
            key_negotiator,
            attestation_type: UnattestedSelf::new(tee_certificate),
        })
    }
}

impl AttestationEngine<UnattestedPeer> {
    pub fn create(expected_tee_measurement: &[u8]) -> anyhow::Result<Self> {
        let key_negotiator = KeyNegotiator::create().context("Couldn't create key negotiator")?;
        Ok(Self {
            key_negotiator,
            attestation_type: UnattestedPeer::new(expected_tee_measurement),
        })
    }
}

impl AttestationEngine<MutuallyUnattested> {
    pub fn create(tee_certificate: &[u8], expected_tee_measurement: &[u8]) -> anyhow::Result<Self> {
        let key_negotiator = KeyNegotiator::create().context("Couldn't create key negotiator")?;
        Ok(Self {
            key_negotiator,
            attestation_type: MutuallyUnattested::new(tee_certificate, expected_tee_measurement),
        })
    }
}
