//
// Copyright 2026 The Project Oak Authors
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

//! What the signer and the verifier have to agree on.

pub mod envelope;
pub mod flags;
pub mod statement;

#[cfg(test)]
mod tests;

/// Audience of the Confidential Space token. Unique to this tool, so a token
/// minted here cannot be replayed into another Oak protocol.
///
/// TODO: b/332507214 - Move next to `OAK_SESSION_NOISE_V1_AUDIENCE` in
/// `oak_attestation_gcp`.
pub const AUDIENCE: &str = "d0f9a3c1-6e57-4b82-9a1d-7c53e8b26f4a";
