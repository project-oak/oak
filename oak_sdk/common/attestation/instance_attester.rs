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

use oak_attestation_types::attester::Attester;
use oak_proto_rust::oak::attestation::v1::Evidence;

/// A simple [`Attester`] that always returns the same finalized [`Evidence`].
///
/// The [`extend`] method is not supported for this type.
///
/// A typical use case of this sort of attester is in Oak Containers
/// applications that receive a finalized Evidence from the Orchestrator.
pub struct InstanceAttester {
    evidence: Evidence,
}

impl InstanceAttester {
    /// Create a new [`InstanceAttester`].
    ///
    /// It will always return the provided [`Evidence`].
    pub fn new(evidence: Evidence) -> Self {
        Self { evidence }
    }
}

impl Attester for InstanceAttester {
    fn extend(&mut self, _encoded_event: &[u8]) -> anyhow::Result<()> {
        anyhow::bail!("This attester type is finalized and can not be extended.");
    }

    /// Return the finalized [`Evidence`] instance.
    fn quote(&self) -> anyhow::Result<Evidence> {
        Ok(self.evidence.clone())
    }
}
