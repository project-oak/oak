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

//! Deserialization types for the Wycheproof AEAD test vector JSON format.
//!
//! These types correspond to the schema defined in
//! `aead_test_schema_v1.json`, documented at
//! <https://github.com/google/wycheproof/blob/master/doc/files.md>.
//!
//! Only the fields needed by the test runner are included; unknown fields
//! are silently ignored to tolerate schema extensions.

use serde::Deserialize;

/// Top-level test file.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
#[allow(dead_code)]
pub struct AeadTestFile {
    /// The algorithm being tested (e.g. `"AES-GCM"`).
    pub algorithm: String,

    /// Total number of test vectors across all groups.
    pub number_of_tests: u32,

    /// Groups of test vectors sharing the same key/IV/tag sizes.
    pub test_groups: Vec<AeadTestGroup>,
}

/// A group of test vectors with common parameters.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
#[allow(dead_code)]
pub struct AeadTestGroup {
    /// IV size in bits.
    pub iv_size: u32,

    /// Key size in bits.
    pub key_size: u32,

    /// Authentication tag size in bits.
    pub tag_size: u32,

    /// Individual test cases.
    pub tests: Vec<AeadTestVector>,
}

/// A single AEAD test vector.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
#[allow(dead_code)]
pub struct AeadTestVector {
    /// Unique test case identifier.
    pub tc_id: u32,

    /// Description of the test case.
    pub comment: String,

    /// Hex-encoded encryption key.
    pub key: String,

    /// Hex-encoded initialization vector / nonce.
    pub iv: String,

    /// Hex-encoded additional authenticated data.
    pub aad: String,

    /// Hex-encoded plaintext.
    pub msg: String,

    /// Hex-encoded ciphertext (without the tag).
    pub ct: String,

    /// Hex-encoded authentication tag.
    pub tag: String,

    /// Expected outcome: `"valid"`, `"invalid"`, or `"acceptable"`.
    pub result: TestResult,

    /// Flags referencing entries in the top-level notes map.
    pub flags: Vec<String>,
}

/// Expected outcome for a test vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TestResult {
    /// The test vector is valid; decryption must succeed and produce the
    /// given plaintext.
    Valid,

    /// The test vector is invalid; decryption must fail.
    Invalid,

    /// Implementation-dependent; may accept or reject.
    Acceptable,
}
