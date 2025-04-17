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

/// Random IDs for commonly used attestation types.

/// Attestation type where the session binding key is signed by a key known to
/// the client.
#[allow(dead_code)]
pub const SIGNATURE_BASED_ATTESTATION_ID: [u8; 16] =
    [81, 54, 249, 225, 240, 173, 71, 33, 181, 68, 99, 119, 220, 60, 71, 3];
