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

use crate::report::{AttestationInfo, Report};
use anyhow::{anyhow, Context};
use serde::{Deserialize, Serialize};

const KEYING_MATERIAL_PURPOSE: &str = "TLSAttestationV1";
const KEYING_MATERIAL_CLIENT_LABEL: &str =
    "EXPERIMENTAL Google Confidential Computing Client Attestation 1.0";
const KEYING_MATERIAL_SERVER_LABEL: &str =
    "EXPERIMENTAL Google Confidential Computing Server Attestation 1.0";
const KEYING_MATERIAL_LENGTH: usize = 128;
// TODO(#2048): Implement multiple assertion types and assertion negotiation.
const ASSERTION_TYPE: &str = "amd_sev_snp_report";

/// Assertion used for remote attestation.
#[derive(Serialize, Deserialize)]
pub struct Assertion {
    attestation_info: AttestationInfo,
}

impl Assertion {
    /// Generates assertion by putting `keying_material` into a TEE report and attaching
    /// `tee_certificate` used to verify the correctness of the TEE report.
    pub fn generate(
        tee_certificate: &[u8],
        keying_material: KeyingMaterial,
    ) -> anyhow::Result<Self> {
        let serialized_keying_material = serde_json::to_string(&keying_material)
            .context("Couldn't serialize keying material")?;
        let tee_report = Report::new(serialized_keying_material.as_bytes());
        let attestation_info = AttestationInfo {
            report: tee_report,
            certificate: tee_certificate.to_vec(),
        };

        Ok(Self { attestation_info })
    }

    /// Verify remote attestation assertion by verifying the TEE report and checking that it
    /// contains `expected_keying_material`.
    pub fn verify(&self, expected_keying_material: &KeyingMaterial) -> anyhow::Result<()> {
        self.attestation_info
            .verify()
            .context("Incorrect attestation info")?;

        let serialized_expected_keying_material = serde_json::to_string(expected_keying_material)
            .context("Couldn't serialize keying material")?;
        if serialized_expected_keying_material.as_bytes() == self.attestation_info.report.data {
            Ok(())
        } else {
            Err(anyhow!("Incorrect keying material"))
        }
    }

    pub fn from_string(input: &str) -> anyhow::Result<Self> {
        serde_json::from_str(input).context("Couldn't deserialize assertion")
    }

    pub fn to_string(&self) -> anyhow::Result<String> {
        serde_json::to_string(&self).context("Couldn't serialize assertion")
    }
}

/// Value uniquely derived from the TLS master secret that is shared by both participants of the TLS
/// session. Used to bind remote attestation to each TLS session independently.
/// https://tools.ietf.org/html/rfc5705
#[derive(Clone, Serialize, Deserialize, PartialEq)]
pub struct KeyingMaterial {
    /// Value used to disambiguate the proper use of the `KeyingMaterial`.
    purpose: String,
    /// Pseudo-random value that is uniquely exported for an individual TLS session.
    value: Vec<u8>,
}

impl KeyingMaterial {
    /// Exports `KeyingMaterial` for a given TLS `session`.
    /// https://tools.ietf.org/html/rfc5705#section-4
    fn export(
        // TLS session used to export `KeyingMaterial` from.
        session: &dyn rustls::Session,
        // Label value that is needed to distinguish between application level protocols that rely
        // on `KeyingMaterial`.
        label: &str,
        // Context value that is used to derive separate `KeyingMaterial` for different assertion
        // types.
        assertion_type: &str,
    ) -> anyhow::Result<Self> {
        let mut buffer = vec![0; KEYING_MATERIAL_LENGTH];
        session
            .export_keying_material(
                &mut buffer,
                label.as_bytes(),
                Some(assertion_type.as_bytes()),
            )
            .context("Couldn't export keying material")?;
        Ok(Self {
            // Purpose value is used to disambiguate the proper use of the `KeyingMaterial`. In this
            // case the usage is remote attestation via TLS.
            purpose: KEYING_MATERIAL_PURPOSE.to_string(),
            value: buffer,
        })
    }
}

/// Convenience structure for exporting keying material with client and server labels.
#[derive(Clone)]
pub struct KeyingMaterialBundle {
    pub client_keying_material: KeyingMaterial,
    pub server_keying_material: KeyingMaterial,
}

impl KeyingMaterialBundle {
    pub fn export(session: &dyn rustls::Session) -> anyhow::Result<Self> {
        Ok(Self {
            client_keying_material: KeyingMaterial::export(
                session,
                KEYING_MATERIAL_CLIENT_LABEL,
                ASSERTION_TYPE,
            )?,
            server_keying_material: KeyingMaterial::export(
                session,
                KEYING_MATERIAL_SERVER_LABEL,
                ASSERTION_TYPE,
            )?,
        })
    }
}
