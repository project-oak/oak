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

pub mod certificate;
pub mod keying_material;
pub mod report;
#[cfg(test)]
mod tests;

use sha2::{digest::Digest, Sha256};

/// Computes a SHA-256 digest of `input` and returns it in a form of raw bytes.
pub fn get_sha256(input: &[u8]) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(&input);
    hasher.finalize().to_vec()
}
