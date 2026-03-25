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

//! Generates both `cleanroom/example_policy.toml` and a module store
//! (`/tmp/modules/`) from one or more compiled Wasm modules.
//!
//! Each positional argument is a path to a `.wasm` binary. The tool:
//!
//! 1. Computes the SHA-256 digest of each module.
//! 2. Copies each module into `/tmp/modules/sha256/<digest>`.
//! 3. Writes `/tmp/modules/manifest.toml` mapping names → digests.
//! 4. Writes `cleanroom/example_policy.toml` with module entries.
//!
//! Declassification privileges are assigned via an explicit map from
//! module name to categories.  Unlisted modules default to
//! `can_declassify = ["local_repo"]`.

use std::{collections::HashMap, env, fs, path::PathBuf};

use anyhow::Context;
use sha2::{Digest, Sha256};

/// A processed module ready for policy and manifest generation.
struct Module {
    /// Human-readable name derived from the file stem.
    name: String,
    /// Hex-encoded SHA-256 digest.
    digest: String,
    /// Categories this module is allowed to declassify.
    can_declassify: Vec<String>,
}

fn main() -> anyhow::Result<()> {
    // Explicit map from module name to declassification privileges.
    let privileges: HashMap<&str, Vec<&str>> = HashMap::from([
        ("to_uppercase_wasm", vec!["local_repo"]),
        ("redact_secret_wasm", vec!["secret_category"]),
        ("weather_wasm", vec!["user_location"]),
    ]);

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

        let name = wasm_path
            .file_stem()
            .and_then(|s| s.to_str())
            .map(|s| s.trim_end_matches(".wasm").to_string())
            .unwrap_or_else(|| "unknown".to_string());

        let can_declassify: Vec<String> = privileges
            .get(name.as_str())
            .map(|cats| cats.iter().map(|s| s.to_string()).collect())
            .unwrap_or_else(|| vec!["local_repo".to_string()]);

        // Copy the module binary into the content-addressed store.
        // Since the filename *is* the digest, an existing file with the same
        // name must have the same content. Verify by size and skip the copy.
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
            println!("  {} → sha256:{} (already in store)", name, digest_hex);
        } else {
            fs::write(&dest, &wasm_bytes)
                .with_context(|| format!("writing {} to store", wasm_path.display()))?;
            println!("  {} → sha256:{}", name, digest_hex);
        }

        modules.push(Module { name, digest: digest_hex, can_declassify });
    }

    // Generate manifest.toml for the module store.
    let mut manifest = String::from("[modules]\n");
    for m in &modules {
        manifest.push_str(&format!("{} = \"sha256:{}\"\n", m.name, m.digest));
    }
    let manifest_path = module_store.join("manifest.toml");
    fs::write(&manifest_path, &manifest)
        .with_context(|| format!("writing manifest to {}", manifest_path.display()))?;

    // Generate example_policy.toml.
    let mut policy = String::new();

    for m in &modules {
        let declassify_list =
            m.can_declassify.iter().map(|s| format!("\"{}\"", s)).collect::<Vec<_>>().join(", ");
        policy.push_str(&format!(
            r#"[[module]]
name           = "{}"
digest         = "sha256:{}"
can_declassify = [{}]

"#,
            m.name, m.digest, declassify_list
        ));
    }

    let policy_path = workspace_dir.join("cleanroom").join("example_policy.toml");
    fs::write(&policy_path, &policy)
        .with_context(|| format!("writing policy to {}", policy_path.display()))?;

    println!();
    println!("Generated:");
    println!("  Policy:   {}", policy_path.display());
    println!("  Manifest: {}", manifest_path.display());
    println!("  Store:    {}", store_dir.display());

    Ok(())
}
