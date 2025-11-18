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

/// Trait that provides the ability to build an attestation evidence with
/// transparent encoded evidence.
///
/// Note that this trait is forked from the existing Attester trait in
/// `oak_attestation_types/src/transparent_attestater.rs`.
///
/// <https://datatracker.ietf.org/doc/html/rfc9334#name-attester>
pub trait TransparentAttester: Send + Sync {
    /// Add a new event to the evidence. Both the original encoded event and the
    /// transparent encoded event should correspond to the same event. The
    /// original event contains potentially sensitive data, the transparent
    /// event has no sensitive data and can be shared externally.
    /// TODO: b/452735395 - Change method name to `extend_transparent`
    fn extend(
        &mut self,
        original_encoded_event: &[u8],
        transparent_encoded_event: &[u8],
    ) -> anyhow::Result<()>;
}
