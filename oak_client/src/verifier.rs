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

pub trait EvidenceProvider {
    fn get_evidence(&mut self) -> anyhow::Result<Evidence>;
}

/// Attestation evidence used to verify the validity of the Trusted Execution
/// Environment and the binary running on it.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-evidence>
pub struct Evidence {
    pub enclave_public_key: Vec<u8>,
}

/// Reference values used by the verifier to appraise the attestation evidence.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-reference-values>
pub struct ReferenceValue {
    pub binary_hash: String,
}

/// Verifier that appraises the attestation evidence and produces an attestation
/// result.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-verifier>
pub trait Verifier {
    fn verify(&self, evidence: &Evidence, reference_value: &ReferenceValue) -> anyhow::Result<()>;
}

pub struct AmdSevSnpVerifier {}

impl Verifier for AmdSevSnpVerifier {
    fn verify(
        &self,
        _evidence: &Evidence,
        _reference_value: &ReferenceValue,
    ) -> anyhow::Result<()> {
        Ok(())
    }
}
