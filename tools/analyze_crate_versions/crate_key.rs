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

//! A versioned crate identifier extracted from Bazel lock file repo names.

use std::{borrow::Borrow, fmt};

/// A versioned crate identifier like `"serde-1.0.228"`.
///
/// Splits at the last hyphen to separate the crate name from its version,
/// handling crate names that contain hyphens (e.g., `"aes-gcm-0.10.3"`).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CrateKey(String);

impl CrateKey {
    pub fn new(key: impl Into<String>) -> Self {
        Self(key.into())
    }

    /// The crate name portion (e.g., `"serde"` from `"serde-1.0.228"`).
    pub fn name(&self) -> &str {
        self.split().map(|(name, _)| name).unwrap_or(&self.0)
    }

    /// The version portion (e.g., `"1.0.228"` from `"serde-1.0.228"`).
    pub fn version(&self) -> &str {
        self.split().map(|(_, version)| version).unwrap_or("?")
    }

    /// The version portion parsed as a [`semver::Version`], if valid.
    pub fn semver_version(&self) -> Option<semver::Version> {
        semver::Version::parse(self.version()).ok()
    }

    fn split(&self) -> Option<(&str, &str)> {
        let (name, version) = self.0.rsplit_once('-')?;
        version.starts_with(|c: char| c.is_ascii_digit()).then_some((name, version))
    }
}

impl fmt::Display for CrateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Borrow<str> for CrateKey {
    fn borrow(&self) -> &str {
        &self.0
    }
}
