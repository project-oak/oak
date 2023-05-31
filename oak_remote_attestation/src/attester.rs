//
// Copyright 2023 The Project Oak Authors
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

use crate::proto::oak::session::v1::AttestationEvidence;
use alloc::vec::Vec;

/// Reference values used by the verifier to appraise the attestation evidence.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-reference-values>
pub struct ReferenceValue {
    pub binary_hash: Vec<u8>,
}

/// A trait implementing the functionality of an attester that generates an attestation evidence.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-attester>
pub trait Attester: Send + Sync {
    /// Generate an attestation evidence containing a remote attestation report and ensuring that
    /// `attested_data` is cryptographically bound to the result (e.g. via a signature).
    fn generate_attestation_evidence(&self, attested_data: &[u8]) -> anyhow::Result<AttestationEvidence>;
}

/// An instance of [`Attester`] that always returns an empty attestation.
///
/// Useful when no attestation report is expected to be genereated by the current side of a remotely
/// attested connection.
#[derive(Clone)]
pub struct EmptyAttester;

impl Attester for EmptyAttester {
    fn generate_attestation_evidence(&self, _attested_data: &[u8]) -> anyhow::Result<AttestationEvidence> {
        Ok(AttestationEvidence {
            attestation_report: Vec::new(),
        })
    }
}
