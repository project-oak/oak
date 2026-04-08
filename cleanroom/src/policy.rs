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

//! Policy file parser for cleanroom IFC.
//!
//! The policy is a TOML file that configures the entire IFC
//! environment for a cleanroom session. It defines:
//! - **Modules**: Wasm modules identified by content digest, each with a
//!   human-readable name and a [`Privilege`](crate::ifc::Privilege).
//!
//! # Why TOML?
//!
//! TOML was chosen over JSON/YAML because it is the standard
//! configuration format in the Rust ecosystem (Cargo.toml, etc.) and
//! supports comments — important for a security-critical config file
//! where annotating *why* a module has certain privileges is valuable.
//!
//! # Security model
//!
//! The policy file is part of the **Trusted Computing Base (TCB)**.
//! It must be:
//!
//! - Readable by the cleanroom server.
//! - **Not writable** by the agent or modules.
//! - Reviewed as carefully as source code — it defines who can declassify what.
//!
//! # Example
//!
//! ```toml
//! # crate_vendor — reads Cargo.lock, fetches crates.
//! [[module]]
//! name           = "crate_vendor"
//! digest         = "sha256:aaa..."
//! can_declassify = ["local_repo"]
//! ```

use std::{collections::HashMap, path::Path};

use anyhow::{Context, Result};
use serde::Deserialize;

use crate::ifc::{Label, Principal, Privilege};

// ── TOML schema types ────────────────────────────────────────────
//
// These types mirror the TOML structure.  They are deserialized and
// then converted into the indexed [`Policy`] for fast lookups.

/// Top-level policy file structure.
#[derive(Debug, Deserialize)]
pub struct PolicyFile {
    /// Module definitions with declassification privileges.
    #[serde(default)]
    pub module: Vec<ModuleConfig>,
}

/// Top-level cells file structure.
///
/// This is a separate TOML file from the policy, containing named
/// data cells that modules can read via the `get-cell` WIT interface.
/// Each cell carries an IFC label that taints the reading module's
/// computation context.
#[derive(Debug, Deserialize)]
pub struct CellsFile {
    /// Named data cells.
    #[serde(default)]
    pub cell: Vec<CellConfig>,
}

/// Configuration for a named cell.
#[derive(Debug, Deserialize, Clone)]
pub struct CellConfig {
    pub name: String,
    pub value: String,
    /// Secrecy principals for this cell's label.
    #[serde(default)]
    pub secrecy: Vec<String>,
    /// Integrity principals for this cell's label.
    #[serde(default)]
    pub integrity: Vec<String>,
}

/// Configuration for a Wasm module.
#[derive(Debug, Deserialize)]
pub struct ModuleConfig {
    /// Human-readable name for the module (e.g. `crate_vendor`).
    pub name: String,
    /// Content digest in `algorithm:hex` format (e.g. `sha256:e3b0c44...`).
    pub digest: String,
    /// Principals this module is privileged to declassify.
    #[serde(default)]
    pub can_declassify: Vec<String>,
}

/// Parsed and indexed policy, ready for lookups.
///
/// This is the result of parsing and indexing a [`PolicyFile`].  It
/// provides O(1) lookups by digest, name, and cell name.
#[derive(Debug, Clone, Default)]
pub struct Policy {
    pub modules_by_digest: HashMap<String, ResolvedModule>,
    /// Map from name to digest for name-based lookup.
    pub digest_by_name: HashMap<String, String>,
    /// Map from cell name to its value and label.
    pub cells: HashMap<String, (String, Label)>,
}

/// A module entry with parsed label and privilege data.
#[derive(Debug, Clone)]
pub struct ResolvedModule {
    /// Human-readable name.
    pub name: String,
    /// Content digest.
    pub digest: String,
    /// Privilege granted to this module.
    pub privilege: Privilege,
}

impl Policy {
    /// Parses a policy from a TOML file at the given path.
    pub fn from_file(path: &Path) -> Result<Self> {
        let contents = std::fs::read_to_string(path)
            .with_context(|| format!("reading policy file {path:?}"))?;
        Self::from_toml(&contents)
    }

    /// Parses a policy from a TOML string.
    pub fn from_toml(toml_str: &str) -> Result<Self> {
        let file: PolicyFile = toml::from_str(toml_str).context("parsing policy TOML")?;
        let mut modules_by_digest = HashMap::new();
        let mut digest_by_name = HashMap::new();

        for m in &file.module {
            let resolved = ResolvedModule {
                name: m.name.clone(),
                digest: m.digest.clone(),
                privilege: Privilege::for_declassification(
                    m.can_declassify.iter().map(Principal::new),
                ),
            };
            modules_by_digest.insert(m.digest.clone(), resolved);
            digest_by_name.insert(m.name.clone(), m.digest.clone());
        }

        Ok(Policy { modules_by_digest, digest_by_name, cells: HashMap::new() })
    }

    /// Loads cells from a separate TOML file and merges them into the
    /// policy.
    pub fn load_cells_file(&mut self, path: &Path) -> Result<()> {
        let contents = std::fs::read_to_string(path)
            .with_context(|| format!("reading cells file {path:?}"))?;
        self.load_cells_toml(&contents)
    }

    /// Parses cells from a TOML string and merges them into the policy.
    pub fn load_cells_toml(&mut self, toml_str: &str) -> Result<()> {
        let file: CellsFile = toml::from_str(toml_str).context("parsing cells TOML")?;
        for c in &file.cell {
            let label = Label::new(
                c.secrecy.iter().map(Principal::new),
                c.integrity.iter().map(Principal::new),
            );
            self.cells.insert(c.name.clone(), (c.value.clone(), label));
        }
        Ok(())
    }

    /// Looks up a module by its content digest.
    pub fn module_by_digest(&self, digest: &str) -> Option<&ResolvedModule> {
        self.modules_by_digest.get(digest)
    }

    /// Looks up a module by its human-readable name.
    pub fn module_by_name(&self, name: &str) -> Option<&ResolvedModule> {
        self.digest_by_name.get(name).and_then(|d| self.modules_by_digest.get(d))
    }

    pub fn modules(&self) -> impl Iterator<Item = &ResolvedModule> {
        self.modules_by_digest.values()
    }

    /// Looks up a cell by name.
    pub fn get_cell(&self, name: &str) -> Option<&(String, Label)> {
        self.cells.get(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A complete example policy for testing.
    const EXAMPLE_POLICY: &str = r#"

# crate_vendor — reads Cargo.lock, fetches crates.
[[module]]
name           = "crate_vendor"
digest         = "sha256:aaa111"
can_declassify = ["local_repo"]

# github_publish — pushes code to GitHub.
[[module]]
name           = "github_publish"
digest         = "sha256:bbb222"
can_declassify = ["local_repo", "github"]

# google_calendar_read — fetches calendar data.
[[module]]
name           = "google_calendar_read"
digest         = "sha256:ccc333"
can_declassify = ["google_calendar"]
"#;

    #[test]
    fn module_lookup_by_digest() {
        let policy = Policy::from_toml(EXAMPLE_POLICY).unwrap();
        let m = policy.module_by_digest("sha256:aaa111").unwrap();

        assert_eq!(m.name, "crate_vendor");
        assert!(
            m.privilege.covers_declassify(&[Principal::new("local_repo")].into_iter().collect())
        );
        assert!(!m.privilege.covers_declassify(&[Principal::new("github")].into_iter().collect()));
    }

    #[test]
    fn module_lookup_by_name() {
        let policy = Policy::from_toml(EXAMPLE_POLICY).unwrap();
        let m = policy.module_by_name("github_publish").unwrap();

        assert_eq!(m.digest, "sha256:bbb222");
        assert!(m.privilege.covers_declassify(
            &[Principal::new("local_repo"), Principal::new("github")].into_iter().collect()
        ));
    }

    #[test]
    fn unlisted_module_returns_none() {
        let policy = Policy::from_toml(EXAMPLE_POLICY).unwrap();
        assert!(policy.module_by_digest("sha256:unknown").is_none());
        assert!(policy.module_by_name("unknown_tool").is_none());
    }

    #[test]
    fn cells_with_secrecy_and_integrity() {
        let cells_toml = r#"
[[cell]]
name = "github_api_key"
value = "ghp_xxx"
secrecy = ["github", "tzn"]
integrity = ["github"]
"#;
        let mut policy = Policy::default();
        policy.load_cells_toml(cells_toml).unwrap();
        let (value, label) = policy.get_cell("github_api_key").unwrap();
        assert_eq!(value, "ghp_xxx");
        assert!(label.secrecy_set().contains(&Principal::new("github")));
        assert!(label.secrecy_set().contains(&Principal::new("tzn")));
        assert!(label.integrity_set().contains(&Principal::new("github")));
    }
}
