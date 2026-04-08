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

//! Principals file management for cleanroom IFC.
//!
//! The `principals.toml` file defines a **trust graph** with three
//! kinds of nodes (principals) and explicit `speaks_for` edges:
//!
//! | Kind | Identity field | Purpose |
//! |------|----------------|---------|
//! | **Named** | _(none)_ | Abstract identity, lattice atom |
//! | **SSH key** | `ssh_public_key` | Cryptographic identity |
//! | **Module** | `module_digest` | Code identity (Wasm digest) |
//!
//! Authority flows via the "speaks for" relation: if principal B
//! speaks for principal A, then B can exercise A's authority.  See
//! [Lampson et al. 1992](https://doi.org/10.1145/138873.138874).
//!
//! # Example
//!
//! ```toml
//! [[principal]]
//! name = "tzn"
//!
//! [[principal]]
//! name = "github"
//!
//! [[principal]]
//! name = "tzn-laptop"
//! ssh_public_key = "AAAAC3NzaC1lZDI1NTE5AAAAI..."
//! speaks_for = ["tzn"]
//!
//! [[principal]]
//! name = "crate_vendor"
//! module_digest = "sha256:aaa111..."
//! speaks_for = ["tzn"]
//! ```

use std::{collections::BTreeSet, path::Path};

use anyhow::{Context, Result, bail};
use serde::{Deserialize, Serialize};

use crate::ifc::Principal;

/// The kind of a principal, determined by which identity field is set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrincipalKind {
    /// Abstract identity (no cryptographic backing).
    Named,
    /// Backed by an SSH public key.
    SshKey,
    /// Backed by a Wasm module content digest.
    Module,
}

impl std::fmt::Display for PrincipalKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrincipalKind::Named => write!(f, "named"),
            PrincipalKind::SshKey => write!(f, "ssh"),
            PrincipalKind::Module => write!(f, "module"),
        }
    }
}

/// A single entry in `principals.toml`.
///
/// Exactly one of `ssh_public_key` / `module_digest` may be set.
/// If neither is set, this is a **named principal** (abstract
/// identity used as a lattice atom).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrincipalEntry {
    /// Unique name within the file.
    pub name: String,

    /// Base64-encoded SSH public key (the middle field from a `.pub`
    /// file).  The key type (e.g. `ssh-ed25519`) is encoded within
    /// the base64 blob itself.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ssh_public_key: Option<String>,

    /// Content digest of a Wasm module (e.g. `sha256:aaa111...`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub module_digest: Option<String>,

    /// Names of principals this one speaks for (delegation edges).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub speaks_for: Vec<String>,
}

impl PrincipalEntry {
    /// Returns the kind of this principal based on which identity
    /// field is set.
    pub fn kind(&self) -> PrincipalKind {
        if self.ssh_public_key.is_some() {
            PrincipalKind::SshKey
        } else if self.module_digest.is_some() {
            PrincipalKind::Module
        } else {
            PrincipalKind::Named
        }
    }
}

/// The `principals.toml` file: a trust graph of principals and
/// speaks-for delegations.
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct PrincipalsFile {
    /// The list of principal entries.
    #[serde(default)]
    pub principal: Vec<PrincipalEntry>,
}

impl PrincipalsFile {
    /// Loads and parses a principals file from disk.
    ///
    /// Returns an empty `PrincipalsFile` if the path does not exist.
    pub fn load(path: &Path) -> Result<Self> {
        if !path.exists() {
            return Ok(Self::default());
        }
        let contents = std::fs::read_to_string(path)
            .with_context(|| format!("reading principals file {path:?}"))?;
        let file: PrincipalsFile = toml::from_str(&contents).context("parsing principals TOML")?;
        Ok(file)
    }

    /// Writes the principals file back to disk.
    pub fn save(&self, path: &Path) -> Result<()> {
        let contents = toml::to_string_pretty(self).context("serializing principals TOML")?;
        std::fs::write(path, contents)
            .with_context(|| format!("writing principals file {path:?}"))?;
        Ok(())
    }

    /// Adds a new principal entry.
    ///
    /// # Errors
    ///
    /// Returns an error if a principal with the same name already
    /// exists.
    pub fn add_principal(&mut self, entry: PrincipalEntry) -> Result<()> {
        if self.find_by_name(&entry.name).is_some() {
            bail!("principal \"{}\" already exists", entry.name);
        }
        self.principal.push(entry);
        Ok(())
    }

    /// Finds a principal entry by name.
    pub fn find_by_name(&self, name: &str) -> Option<&PrincipalEntry> {
        self.principal.iter().find(|p| p.name == name)
    }

    /// Finds a principal entry by SSH public key.
    pub fn find_by_key(&self, key: &str) -> Option<&PrincipalEntry> {
        self.principal.iter().find(|p| p.ssh_public_key.as_deref() == Some(key))
    }

    /// Finds a principal entry by module content digest.
    pub fn find_by_digest(&self, digest: &str) -> Option<&PrincipalEntry> {
        self.principal.iter().find(|p| p.module_digest.as_deref() == Some(digest))
    }

    /// Adds a speaks-for delegation: `to` will speak for `from`.
    ///
    /// Both principal names must exist.  The delegation is idempotent
    /// (adding a duplicate edge is a no-op).
    pub fn add_delegation(&mut self, from: &str, to: &str) -> Result<()> {
        if self.find_by_name(from).is_none() {
            bail!("principal \"{from}\" not found");
        }
        let entry = self
            .principal
            .iter_mut()
            .find(|p| p.name == to)
            .with_context(|| format!("principal \"{to}\" not found"))?;
        if !entry.speaks_for.contains(&from.to_string()) {
            entry.speaks_for.push(from.to_string());
        }
        Ok(())
    }

    /// Removes a speaks-for delegation.
    ///
    /// Both principal names must exist.
    pub fn remove_delegation(&mut self, from: &str, to: &str) -> Result<()> {
        if self.find_by_name(from).is_none() {
            bail!("principal \"{from}\" not found");
        }
        let entry = self
            .principal
            .iter_mut()
            .find(|p| p.name == to)
            .with_context(|| format!("principal \"{to}\" not found"))?;
        entry.speaks_for.retain(|s| s != from);
        Ok(())
    }

    /// Resolves the transitive closure of speaks-for for a principal.
    ///
    /// Returns the set containing the principal itself plus all
    /// principals it transitively speaks for.
    ///
    /// Handles cycles without infinite looping.
    pub fn resolve_speaks_for(&self, name: &str) -> BTreeSet<Principal> {
        let mut result = BTreeSet::new();
        let mut stack = vec![name.to_string()];

        while let Some(current) = stack.pop() {
            let principal = Principal::new(&current);
            if result.contains(&principal) {
                continue; // already visited — break cycles
            }
            result.insert(principal);

            if let Some(entry) = self.find_by_name(&current) {
                for target in &entry.speaks_for {
                    stack.push(target.clone());
                }
            }
        }

        result
    }
}

/// Extracts the base64 SSH public key from an OpenSSH `.pub` file.
///
/// The file format is: `<algorithm> <base64-key-data> [comment]`
///
/// Returns the middle field (the base64-encoded key data).  The
/// algorithm identifier (e.g. `ssh-ed25519`) is already encoded
/// within the base64 blob, so it's not needed separately.
pub fn ssh_public_key_from_file(path: &Path) -> Result<String> {
    let contents = std::fs::read_to_string(path)
        .with_context(|| format!("reading SSH public key file {path:?}"))?;
    let line = contents.lines().next().context("empty public key file")?;
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.len() < 2 {
        bail!("invalid SSH public key format, expected: <algo> <base64> [comment]");
    }
    Ok(parts[1].to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn named(name: &str) -> PrincipalEntry {
        PrincipalEntry {
            name: name.to_string(),
            ssh_public_key: None,
            module_digest: None,
            speaks_for: vec![],
        }
    }

    fn ssh_key(name: &str, key: &str) -> PrincipalEntry {
        PrincipalEntry {
            name: name.to_string(),
            ssh_public_key: Some(key.to_string()),
            module_digest: None,
            speaks_for: vec![],
        }
    }

    fn module(name: &str, digest: &str) -> PrincipalEntry {
        PrincipalEntry {
            name: name.to_string(),
            ssh_public_key: None,
            module_digest: Some(digest.to_string()),
            speaks_for: vec![],
        }
    }

    // -- PrincipalKind detection --

    #[test]
    fn kind_named() {
        assert_eq!(named("tzn").kind(), PrincipalKind::Named);
    }

    #[test]
    fn kind_ssh_key() {
        assert_eq!(ssh_key("tzn-laptop", "AAAA...").kind(), PrincipalKind::SshKey);
    }

    #[test]
    fn kind_module() {
        assert_eq!(module("crate_vendor", "sha256:abc").kind(), PrincipalKind::Module);
    }

    // -- Add and lookup --

    #[test]
    fn add_and_find_by_name() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("alice")).unwrap();
        assert!(pf.find_by_name("alice").is_some());
        assert!(pf.find_by_name("bob").is_none());
    }

    #[test]
    fn add_duplicate_name_fails() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("alice")).unwrap();
        assert!(pf.add_principal(named("alice")).is_err());
    }

    #[test]
    fn find_by_key() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(ssh_key("laptop", "AAAA_KEY")).unwrap();
        assert_eq!(pf.find_by_key("AAAA_KEY").unwrap().name, "laptop");
        assert!(pf.find_by_key("OTHER").is_none());
    }

    #[test]
    fn find_by_digest() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(module("my_mod", "sha256:abc")).unwrap();
        assert_eq!(pf.find_by_digest("sha256:abc").unwrap().name, "my_mod");
        assert!(pf.find_by_digest("sha256:other").is_none());
    }

    // -- Delegation --

    #[test]
    fn add_delegation() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("alice")).unwrap();
        pf.add_principal(named("bob")).unwrap();
        pf.add_delegation("alice", "bob").unwrap();

        let bob = pf.find_by_name("bob").unwrap();
        assert_eq!(bob.speaks_for, vec!["alice"]);
    }

    #[test]
    fn add_delegation_idempotent() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("alice")).unwrap();
        pf.add_principal(named("bob")).unwrap();
        pf.add_delegation("alice", "bob").unwrap();
        pf.add_delegation("alice", "bob").unwrap(); // duplicate

        let bob = pf.find_by_name("bob").unwrap();
        assert_eq!(bob.speaks_for, vec!["alice"]);
    }

    #[test]
    fn add_delegation_unknown_from_fails() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("bob")).unwrap();
        assert!(pf.add_delegation("unknown", "bob").is_err());
    }

    #[test]
    fn add_delegation_unknown_to_fails() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("alice")).unwrap();
        assert!(pf.add_delegation("alice", "unknown").is_err());
    }

    #[test]
    fn remove_delegation() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("alice")).unwrap();
        pf.add_principal(named("bob")).unwrap();
        pf.add_delegation("alice", "bob").unwrap();
        pf.remove_delegation("alice", "bob").unwrap();

        let bob = pf.find_by_name("bob").unwrap();
        assert!(bob.speaks_for.is_empty());
    }

    // -- Transitive resolution --

    #[test]
    fn resolve_speaks_for_self_only() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("alice")).unwrap();

        let resolved = pf.resolve_speaks_for("alice");
        assert_eq!(resolved.len(), 1);
        assert!(resolved.contains(&Principal::new("alice")));
    }

    #[test]
    fn resolve_speaks_for_direct() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("alice")).unwrap();
        pf.add_principal(ssh_key("laptop", "AAAA")).unwrap();
        pf.add_delegation("alice", "laptop").unwrap();

        let resolved = pf.resolve_speaks_for("laptop");
        assert!(resolved.contains(&Principal::new("laptop")));
        assert!(resolved.contains(&Principal::new("alice")));
    }

    #[test]
    fn resolve_speaks_for_transitive() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("root")).unwrap();
        pf.add_principal(named("middle")).unwrap();
        pf.add_principal(named("leaf")).unwrap();
        pf.add_delegation("root", "middle").unwrap();
        pf.add_delegation("middle", "leaf").unwrap();

        let resolved = pf.resolve_speaks_for("leaf");
        assert!(resolved.contains(&Principal::new("leaf")));
        assert!(resolved.contains(&Principal::new("middle")));
        assert!(resolved.contains(&Principal::new("root")));
    }

    #[test]
    fn resolve_speaks_for_handles_cycles() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("a")).unwrap();
        pf.add_principal(named("b")).unwrap();
        pf.add_delegation("b", "a").unwrap();
        pf.add_delegation("a", "b").unwrap();

        // Should terminate despite cycle.
        let resolved = pf.resolve_speaks_for("a");
        assert!(resolved.contains(&Principal::new("a")));
        assert!(resolved.contains(&Principal::new("b")));
    }

    #[test]
    fn resolve_speaks_for_multiple_targets() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("alice")).unwrap();
        pf.add_principal(named("github")).unwrap();
        pf.add_principal(module("publisher", "sha256:bbb")).unwrap();
        pf.add_delegation("alice", "publisher").unwrap();
        pf.add_delegation("github", "publisher").unwrap();

        let resolved = pf.resolve_speaks_for("publisher");
        assert!(resolved.contains(&Principal::new("publisher")));
        assert!(resolved.contains(&Principal::new("alice")));
        assert!(resolved.contains(&Principal::new("github")));
    }

    #[test]
    fn resolve_unknown_principal() {
        let pf = PrincipalsFile::default();
        let resolved = pf.resolve_speaks_for("nobody");
        // Still returns {nobody} even if not in the file.
        assert_eq!(resolved.len(), 1);
        assert!(resolved.contains(&Principal::new("nobody")));
    }

    // -- TOML round-trip --

    #[test]
    fn toml_round_trip() {
        let mut pf = PrincipalsFile::default();
        pf.add_principal(named("alice")).unwrap();
        pf.add_principal(ssh_key("laptop", "AAAA_KEY")).unwrap();
        pf.add_principal(module("my_mod", "sha256:abc")).unwrap();
        pf.add_delegation("alice", "laptop").unwrap();
        pf.add_delegation("alice", "my_mod").unwrap();

        let toml_str = toml::to_string_pretty(&pf).expect("serialize");
        let pf2: PrincipalsFile = toml::from_str(&toml_str).expect("deserialize");

        assert_eq!(pf2.principal.len(), 3);
        assert_eq!(pf2.find_by_name("laptop").unwrap().speaks_for, vec!["alice"]);
        assert_eq!(
            pf2.find_by_name("my_mod").unwrap().module_digest,
            Some("sha256:abc".to_string())
        );
    }

    // -- ssh_public_key_from_file --

    #[test]
    fn extract_key_from_pub_file() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test.pub");
        std::fs::write(&path, "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIGdSI1w user@host\n").unwrap();

        let key = ssh_public_key_from_file(&path).unwrap();
        assert_eq!(key, "AAAAC3NzaC1lZDI1NTE5AAAAIGdSI1w");
    }

    #[test]
    fn extract_key_no_comment() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test.pub");
        std::fs::write(&path, "ssh-ed25519 AAAAC3Nz\n").unwrap();

        let key = ssh_public_key_from_file(&path).unwrap();
        assert_eq!(key, "AAAAC3Nz");
    }

    #[test]
    fn extract_key_invalid_format() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test.pub");
        std::fs::write(&path, "justonetoken\n").unwrap();

        assert!(ssh_public_key_from_file(&path).is_err());
    }
}
