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

use alloc::vec::Vec;

use oak_proto_rust::oak::attestation::v1::Evidence;

pub trait Attester {
    // Add a new layer to the evidence containing the event.
    fn extend(&mut self, encoded_event: &[u8]) -> anyhow::Result<()>;

    // Generates a signed Evidence containing all events previously provided with
    // `extend`.
    fn quote(&self) -> anyhow::Result<Evidence>;
}

/// Trait for passing incomplete evidence between layers of software components.
/// For example, in DICE it is used to pass the DiceData containing the
/// certificate authority private key, and for TDX it is used to pass an
/// unfinished EventLog.
pub trait Serializable: Sized {
    fn deserialize(bytes: &[u8]) -> anyhow::Result<Self>;
    fn serialize(self) -> Vec<u8>;
}
