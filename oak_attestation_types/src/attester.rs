//
// Copyright 2024 The Project Oak Authors
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

#[cfg(test)]
use mockall::automock;
use oak_proto_rust::oak::attestation::v1::Evidence;

/// Trait that provides the ability to build an attestation evidence.
///
/// <https://datatracker.ietf.org/doc/html/rfc9334#name-attester>
#[cfg_attr(test, automock)]
pub trait Attester: Send + Sync {
    /// Add a new event to the evidence.
    fn extend(&mut self, encoded_event: &[u8]) -> anyhow::Result<()>;

    /// Generate a signed evidence containing all events previously provided
    /// with `extend`.
    ///
    /// This function doesn't take a mutable reference because quoting shouldn't
    /// change the evidence. Evidence can only be updated via the `extend`
    /// function.
    fn quote(&self) -> anyhow::Result<Evidence>;
}
