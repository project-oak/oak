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

use crate::{
    crypto::{get_sha256, AeadEncryptor, EncryptorType, KeyNegotiator},
    proto::{AttestationIdentity, AttestationInfo, AttestationReport},
};
use anyhow::{anyhow, Context};

/// Remote attestation protocol implementation.
/// Template `S` defines the type of attestation used. It can be one of:
/// - [`UnattestedSelf`]: represents an attestation process, where current machine remotely attests
///   to a remote peer and sends attestation info to it.
/// - [`UnattestedPeer`]: represents an attestation process, where current machine remotely attests
///   a remote peer and verifies its attestation info.
/// - [`MutuallyUnattested`]: represents an attestation process, where current machine and a remote
///   peer remotely attest each other.
pub struct AttestationEngine<S>
where
    S: AttestationType,
{
    /// Type of the remote attestation process.
    attestation_type: S,
    /// Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
    key_negotiator: KeyNegotiator,
}

impl<S> AttestationEngine<S>
where
    S: AttestationType,
{
    /// Returns an [`AttestationIdentity`] that contains a public key and possibly an attestation
    /// info (depending on `Self::attestation_type`).
    pub fn identity(&self) -> anyhow::Result<AttestationIdentity> {
        let public_key = self
            .key_negotiator
            .public_key()
            .context("Couldn't get public key")?;
        let public_key_hash = get_sha256(&public_key);
        let attestation_info = self
            .attestation_type
            .generate_attestation_info(&public_key_hash);

        Ok(AttestationIdentity {
            public_key,
            attestation_info,
        })
    }

    /// Verifies remote attestation, negotiates session keys and creates server [`AeadEncryptor`].
    ///
    /// Server encryptor uses server session key for encryption and client session key for
    /// decryption.
    pub fn create_server_encryptor(
        self,
        peer_identity: &AttestationIdentity,
    ) -> anyhow::Result<AeadEncryptor> {
        // Verify peer attestation info.
        let peer_attestation_info = &peer_identity.attestation_info;
        self.attestation_type
            .verify_attestation_info(&peer_attestation_info)
            .context("Couldn't verify peer attestation info")?;

        // Agree on session keys and create encryptor.
        self.key_negotiator
            .create_encryptor(peer_identity.public_key.as_ref(), EncryptorType::Server)
            .context("Couldn't derive session key")
    }

    /// Verifies remote attestation, negotiates session keys and creates client [`AeadEncryptor`].
    ///
    /// Client encryptor uses client session key for encryption and server session key for
    /// decryption.
    pub fn create_client_encryptor(
        self,
        peer_identity: &AttestationIdentity,
    ) -> anyhow::Result<AeadEncryptor> {
        // Verify peer attestation info.
        let peer_attestation_info = &peer_identity.attestation_info;
        self.attestation_type
            .verify_attestation_info(&peer_attestation_info)
            .context("Couldn't verify peer attestation info")?;

        // Agree on session keys and create encryptor.
        self.key_negotiator
            .create_encryptor(peer_identity.public_key.as_ref(), EncryptorType::Client)
            .context("Couldn't derive session key")
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

/// Represents an attestation process, where current machine remotely attests to a remote peer and
/// sends attestation info to it.
pub struct UnattestedSelf {
    /// PEM encoded X.509 certificate that signs TEE firmware key.
    tee_certificate: Vec<u8>,
}

impl UnattestedSelf {
    pub fn new(tee_certificate: &[u8]) -> Self {
        Self {
            tee_certificate: tee_certificate.to_vec(),
        }
    }
}

/// Represents an attestation process, where current machine remotely attests a remote peer and
/// verifies its attestation info.
pub struct UnattestedPeer {
    /// Expected value of the peer's TEE measurement.
    expected_tee_measurement: Vec<u8>,
}

impl UnattestedPeer {
    pub fn new(expected_tee_measurement: &[u8]) -> Self {
        Self {
            expected_tee_measurement: expected_tee_measurement.to_vec(),
        }
    }
}

/// Represents an attestation process, where current machine and a remote peer remotely attest each
/// other.
pub struct MutuallyUnattested {
    /// PEM encoded X.509 certificate that signs TEE firmware key.
    tee_certificate: Vec<u8>,
    /// Expected value of the peer's TEE measurement.
    expected_tee_measurement: Vec<u8>,
}

impl MutuallyUnattested {
    pub fn new(tee_certificate: &[u8], expected_tee_measurement: &[u8]) -> Self {
        Self {
            tee_certificate: tee_certificate.to_vec(),
            expected_tee_measurement: expected_tee_measurement.to_vec(),
        }
    }
}

/// Defines remote attestation behavior between this machine and a peer.
pub trait AttestationType {
    /// Generates attestation info if trait implementor can be remotely attested a peer.
    fn generate_attestation_info(&self, public_key_hash: &[u8]) -> Option<AttestationInfo>;
    /// Verifies peer attestation info if trait implementor can remotely attest a peer.
    fn verify_attestation_info(
        self,
        peer_attestation_info: &Option<AttestationInfo>,
    ) -> anyhow::Result<()>;
}

impl AttestationType for UnattestedSelf {
    fn generate_attestation_info(&self, public_key_hash: &[u8]) -> Option<AttestationInfo> {
        // Generate attestation info with a TEE report.
        // TEE report contains a hash of the public key.
        Some(AttestationInfo {
            report: Some(AttestationReport::new(&public_key_hash)),
            certificate: self.tee_certificate.clone(),
        })
    }

    /// This type of attestation doesn't need to verify peer attestation, since it will be attested
    /// by peer.
    fn verify_attestation_info(
        self,
        _peer_attestation_info: &Option<AttestationInfo>,
    ) -> anyhow::Result<()> {
        Ok(())
    }
}

impl AttestationType for UnattestedPeer {
    fn generate_attestation_info(&self, _public_key_hash: &[u8]) -> Option<AttestationInfo> {
        None
    }

    fn verify_attestation_info(
        self,
        peer_attestation_info: &Option<AttestationInfo>,
    ) -> anyhow::Result<()> {
        let peer_attestation_info = peer_attestation_info
            .as_ref()
            .context("No attestation info provided")?;
        verify_attestation(&peer_attestation_info, &self.expected_tee_measurement)
            .context("Couldn't verify peer attestation info")
    }
}

impl AttestationType for MutuallyUnattested {
    fn generate_attestation_info(&self, public_key_hash: &[u8]) -> Option<AttestationInfo> {
        // Generate attestation info with a TEE report.
        // TEE report contains a hash of the public key.
        Some(AttestationInfo {
            report: Some(AttestationReport::new(&public_key_hash)),
            certificate: self.tee_certificate.clone(),
        })
    }

    fn verify_attestation_info(
        self,
        peer_attestation_info: &Option<AttestationInfo>,
    ) -> anyhow::Result<()> {
        let peer_attestation_info = peer_attestation_info
            .as_ref()
            .context("No attestation info provided")?;
        verify_attestation(&peer_attestation_info, &self.expected_tee_measurement)
            .context("Couldn't verify peer attestation info")
    }
}

/// Verifies the validity of the attestation info:
/// - Checks that the TEE report is signed by TEE Provider’s root key.
/// - Checks that the public key hash from the TEE report is equal to the hash of the public key
///   presented in the server response.
/// - Extracts the TEE measurement from the TEE report and compares it to the
///   `expected_tee_measurement`.
fn verify_attestation(
    peer_attestation_info: &AttestationInfo,
    expected_tee_measurement: &[u8],
) -> anyhow::Result<()> {
    // TODO(#1867): Add remote attestation support, use real TEE reports and check that
    // `AttestationInfo::certificate` is signed by one of the root certificates.

    // Verify peer tee measurement.
    let peer_report = peer_attestation_info
        .report
        .as_ref()
        .context("Couldn't find report in peer attestation info")?;
    if expected_tee_measurement == peer_report.measurement {
        Ok(())
    } else {
        Err(anyhow!("Incorrect TEE measurement"))
    }
}
