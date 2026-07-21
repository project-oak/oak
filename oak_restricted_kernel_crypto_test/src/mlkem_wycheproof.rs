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

//! Deserialization types for the Wycheproof ML-KEM test vector JSON format.
//!
//! These types cover the two ML-KEM vector families exercised by this test,
//! documented at
//! <https://github.com/google/wycheproof/blob/master/doc/files.md>:
//!
//! - `mlkem_*_test.json` — key generation from a seed followed by decapsulation
//!   (fields: `seed`, `c`, `K`, optional `ek`).
//! - `mlkem_*_keygen_seed_test.json` — key generation from a seed (fields:
//!   `seed`, `ek`, `dk`).
//!
//! A single [`MlKemTestVector`] with optional fields covers both layouts;
//! fields absent from a given file default to the empty string. Unknown fields
//! are silently ignored to tolerate schema extensions.

use serde::Deserialize;

// Re-use the shared outcome enum and generic test-file wrapper.
pub use crate::wycheproof::{TestFile, TestResult};

/// A Wycheproof ML-KEM test file.
pub type MlKemTestFile = TestFile<MlKemTestGroup>;

/// A group of ML-KEM test vectors sharing a parameter set.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
#[allow(dead_code)]
pub struct MlKemTestGroup {
    /// The parameter set as a Wycheproof string, e.g. `"ML-KEM-768"`.
    pub parameter_set: String,

    /// The kind of test in this group (e.g. `"MLKEMTest"`).
    #[serde(default, rename = "type")]
    pub test_type: String,

    /// Individual test cases.
    pub tests: Vec<MlKemTestVector>,
}

/// A single ML-KEM test vector.
///
/// The set of populated byte fields depends on the file the vector came from;
/// see the module docs. Byte fields are hex-encoded strings and default to the
/// empty string when absent.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
#[allow(dead_code)]
pub struct MlKemTestVector {
    /// Unique test case identifier.
    pub tc_id: u32,

    /// Description of the test case.
    #[serde(default)]
    pub comment: String,

    /// Flags referencing entries in the top-level notes map.
    #[serde(default)]
    pub flags: Vec<String>,

    /// Hex-encoded key-generation seed (`d || z`, 64 bytes).
    #[serde(default)]
    pub seed: String,

    /// Hex-encoded encapsulation (public) key.
    #[serde(default)]
    pub ek: String,

    /// Hex-encoded decapsulation (private) key.
    #[serde(default)]
    pub dk: String,

    /// Hex-encoded ciphertext.
    #[serde(default)]
    pub c: String,

    /// Hex-encoded shared secret `K`.
    #[serde(default, rename = "K")]
    pub shared_secret: String,

    /// Expected outcome: `"valid"`, `"invalid"`, or `"acceptable"`.
    pub result: TestResult,
}
