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

//! Provides a struct representing an endorsement package and verification
//! on it. An endorsement package is a set of serialized pieces of data
//! (files in memory). Since the actual binary is not included, the size of
//! `Package` instances is usually not more than a few kilobytes.

use alloc::{string::String, vec, vec::Vec};

use anyhow::{Context, Result};
use oak_proto_rust::oak::attestation::v1::{EndorsementReferenceValue, SignedEndorsement};
use verify_endorsement::{
    create_endorsement_reference_value, create_signed_endorsement, create_verifying_key_from_pem,
    verify_endorsement,
};

// Due to key rotation the endorser key set could contain multiple verifying
// keys. The purpose of the key ID is to disambiguate between these keys.
// However, it is meaningless in this setting, as we have only one. Just need
// to use the same number in signed endorsement and reference values.
const KEY_ID: u32 = 1;

/// Represents an endorsement package in memory.
pub struct Package {
    /// The endorsement as JSON (contents of endorsement.json).
    pub endorsement: Vec<u8>,

    /// The signature over the endorsement as binary (contents of
    /// endorsement.json.sig).
    pub signature: Vec<u8>,

    /// The log entry related to the signed endorsement if it exists
    /// (contents of logentry.json).
    pub log_entry: Option<Vec<u8>>,

    /// The subject mentioned in the endorsement if it is needed for the
    /// verification.
    pub subject: Option<Vec<u8>>,

    /// The public key for verifying the endorsement signature as PEM.
    pub endorser_public_key: String,

    /// The public key for verifying the log entry signature as PEM.
    pub rekor_public_key: Option<String>,
}

impl Package {
    /// Returns the `SignedEndorsement` proto associated with the package.
    pub fn get_signed_endorsement(&self) -> Result<SignedEndorsement> {
        let subject = match &self.subject {
            None => &vec![],
            Some(array) => array,
        };
        let log_entry = match &self.log_entry {
            None => &vec![],
            Some(array) => array,
        };
        Ok(create_signed_endorsement(
            &self.endorsement,
            &self.signature,
            KEY_ID,
            subject,
            log_entry,
        ))
    }

    /// Returns the reference value associated with the package.
    pub fn get_reference_value(&self) -> EndorsementReferenceValue {
        let endorser_key = create_verifying_key_from_pem(&self.endorser_public_key, KEY_ID);
        let rekor_key =
            self.rekor_public_key.as_ref().map(|pem| create_verifying_key_from_pem(pem, KEY_ID));
        create_endorsement_reference_value(endorser_key, rekor_key)
    }

    /// Verifies the endorsement package.
    pub fn verify(&self, now_utc_millis: i64) -> Result<()> {
        let signed_endorsement = self.get_signed_endorsement()?;
        let ref_value = self.get_reference_value();
        verify_endorsement(now_utc_millis, &signed_endorsement, &ref_value)
            .context("verifying endorsement")
            .map(|_| ())
    }
}
