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

use crate::proto::{AttestationIdentity, AttestationInfo, AttestationReport};
use anyhow::{anyhow, Context};

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

/// Represents an attestation process, where current machine attests and a remote peer remotely
/// attest each other.
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

pub trait UnattestedSession {
    fn get_attestation_info(&self, public_key_hash: &[u8]) -> Option<AttestationInfo>;
    fn verify_attestation(self, peer_identity: &AttestationIdentity) -> anyhow::Result<()>;
}

impl UnattestedSession for UnattestedSelf {
    fn get_attestation_info(&self, public_key_hash: &[u8]) -> Option<AttestationInfo> {
        // Generate attestation info with a TEE report.
        // TEE report contains a hash of the public key.
        Some(AttestationInfo {
            report: Some(AttestationReport::new(&public_key_hash)),
            certificate: self.tee_certificate.clone(),
        })
    }

    fn verify_attestation(self, _peer_identity: &AttestationIdentity) -> anyhow::Result<()> {
        Ok(())
    }
}

impl UnattestedSession for UnattestedPeer {
    fn get_attestation_info(&self, _public_key_hash: &[u8]) -> Option<AttestationInfo> {
        None
    }

    fn verify_attestation(self, peer_identity: &AttestationIdentity) -> anyhow::Result<()> {
        // Verify peer attestation info.
        let peer_attestation_info = peer_identity
            .attestation_info
            .as_ref()
            .context("Peer identity doesn't contain attestation info")?;
        verify_attestation(&peer_attestation_info, &self.expected_tee_measurement)
            .context("Couldn't verify peer attestation info")
    }
}

impl UnattestedSession for MutuallyUnattested {
    fn get_attestation_info(&self, public_key_hash: &[u8]) -> Option<AttestationInfo> {
        // Generate attestation info with a TEE report.
        // TEE report contains a hash of the public key.
        Some(AttestationInfo {
            report: Some(AttestationReport::new(&public_key_hash)),
            certificate: self.tee_certificate.clone(),
        })
    }

    fn verify_attestation(self, peer_identity: &AttestationIdentity) -> anyhow::Result<()> {
        // Verify peer attestation info.
        let peer_attestation_info = peer_identity
            .attestation_info
            .as_ref()
            .context("Peer identity doesn't contain attestation info")?;
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
    peer_attestation_info
        .verify()
        .context("Couldn't verify peer attestation info")?;

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
