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

//! Updates `cleanroom/example_policy.toml` with fresh module digests
//! and populates the module store (`/tmp/modules/`).
//!
//! The tool reads the existing policy file, matches each Wasm module
//! argument to a principal by name, and updates its `module_digest`
//! field in place.  All other fields (speaks_for, SSH keys, named
//! principals) are preserved.  New modules not yet in the policy are
//! appended.
//!
//! Each positional argument is a path to a `.wasm` binary. The tool:
//!
//! 1. Computes the SHA-256 digest of each module.
//! 2. Copies each module into `/tmp/modules/sha256/<digest>`.
//! 3. Writes `/tmp/modules/manifest.toml` mapping names → digests.
//! 4. Updates `cleanroom/example_policy.toml` with current digests.

use std::{env, fs, path::PathBuf};

use anyhow::Context;
use cleanroom_lib::principals::{PrincipalEntry, PrincipalsFile};
use sha2::{Digest, Sha256};

/// A processed module ready for policy and manifest generation.
struct Module {
    /// Human-readable name derived from the file stem.
    name: String,
    /// Full digest string (e.g. "sha256:abcd...").
    digest: String,
}

fn main() -> anyhow::Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        anyhow::bail!("Usage: generate_policy <wasm_module>...");
    }

    // Resolve the workspace root.
    let workspace_dir = env::var("BUILD_WORKSPACE_DIRECTORY")
        .map(PathBuf::from)
        .or_else(|_| env::current_dir())
        .context("getting workspace directory")?;

    let module_store = PathBuf::from("/tmp/modules");
    let store_dir = module_store.join("sha256");
    fs::create_dir_all(&store_dir).context("creating module store directory")?;

    // Process each module argument.
    let mut modules = Vec::new();
    for wasm_arg in &args[1..] {
        let wasm_path = PathBuf::from(wasm_arg);
        let wasm_bytes = fs::read(&wasm_path)
            .with_context(|| format!("reading wasm module from {}", wasm_path.display()))?;

        let mut hasher = Sha256::new();
        hasher.update(&wasm_bytes);
        let digest_hex = format!("{:x}", hasher.finalize());
        let digest = format!("sha256:{digest_hex}");

        let name = wasm_path
            .file_stem()
            .and_then(|s| s.to_str())
            .map(|s| s.trim_end_matches(".wasm").to_string())
            .unwrap_or_else(|| "unknown".to_string());

        // Copy the module binary into the content-addressed store.
        let dest = store_dir.join(&digest_hex);
        if dest.exists() {
            let existing_len = fs::metadata(&dest)
                .with_context(|| format!("reading metadata of {}", dest.display()))?
                .len();
            if existing_len != wasm_bytes.len() as u64 {
                anyhow::bail!(
                    "INTEGRITY ERROR: {} already exists with size {} but expected {}. \
                     The content-addressed store may be corrupted!",
                    dest.display(),
                    existing_len,
                    wasm_bytes.len()
                );
            }
            println!("  {} → {} (already in store)", name, digest);
        } else {
            fs::write(&dest, &wasm_bytes)
                .with_context(|| format!("writing {} to store", wasm_path.display()))?;
            println!("  {} → {}", name, digest);
        }

        modules.push(Module { name, digest });
    }

    // Generate manifest.toml for the module store.
    let mut manifest = String::from("[modules]\n");
    for m in &modules {
        manifest.push_str(&format!("{} = \"{}\"\n", m.name, m.digest));
    }
    let manifest_path = module_store.join("manifest.toml");
    fs::write(&manifest_path, &manifest)
        .with_context(|| format!("writing manifest to {}", manifest_path.display()))?;

    // Read the existing policy file, or start fresh.
    let policy_path = workspace_dir.join("cleanroom").join("example_policy.toml");
    let mut policy = if policy_path.exists() {
        PrincipalsFile::load(&policy_path).context("reading existing policy file")?
    } else {
        PrincipalsFile::default()
    };

    // Update or insert each module's digest.
    for m in &modules {
        if let Some(entry) = policy.principal.iter_mut().find(|p| p.name == m.name) {
            // Update existing entry's digest.
            entry.module_digest = Some(m.digest.clone());
        } else {
            // New module — append with default speaks_for based on known
            // privilege requirements.
            let speaks_for = default_speaks_for(&m.name);
            policy.principal.push(PrincipalEntry {
                name: m.name.clone(),
                module_digest: Some(m.digest.clone()),
                speaks_for,
                ssh_public_key: None,
            });
        }
    }

    // Write the updated policy file.
    policy.save(&policy_path).context("writing policy file")?;

    println!();
    println!("Generated:");
    println!("  Policy:   {}", policy_path.display());
    println!("  Manifest: {}", manifest_path.display());
    println!("  Store:    {}", store_dir.display());

    Ok(())
}

/// Returns the default `speaks_for` list for a newly-discovered module.
///
/// Modules that need to declassify data for outgoing HTTP or output
/// must have privilege over the relevant secrecy principals.  This
/// table encodes those known requirements so that the generated policy
/// is immediately usable.
fn default_speaks_for(module_name: &str) -> Vec<String> {
    match module_name {
        "weather_wasm" => vec!["user_location".to_string()],
        "limited_calendar_wasm" => {
            vec!["calendar_token".to_string(), "alice".to_string()]
        }
        "crate_vendor" => vec!["alice".to_string()],
        _ => vec![],
    }
}
