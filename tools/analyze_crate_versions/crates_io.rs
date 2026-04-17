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
//

//! Crates.io API client and version cache management.

use std::{collections::HashMap, path::Path};

use anyhow::{Context, Result};

use crate::CrateVersionInfo;

/// Fetch all versions of a crate from the crates.io API.
pub fn fetch_crate_versions(crate_name: &str) -> Result<Vec<CrateVersionInfo>> {
    let url = format!("https://crates.io/api/v1/crates/{}", crate_name);
    let response = ureq::get(&url)
        .set("User-Agent", "Oak-Crate-Analyzer/0.1")
        .call()
        .with_context(|| format!("fetching {}", url))?;

    let body = response.into_string()?;
    let data: serde_json::Value = serde_json::from_str(&body)?;

    let versions = data
        .get("versions")
        .and_then(|v| v.as_array())
        .map(|arr| {
            arr.iter()
                .filter_map(|v| {
                    Some(CrateVersionInfo {
                        version: v.get("num")?.as_str()?.to_string(),
                        yanked: v.get("yanked")?.as_bool()?,
                        created_at: v.get("created_at")?.as_str()?.to_string(),
                    })
                })
                .collect()
        })
        .unwrap_or_default();

    Ok(versions)
}

/// Load the version cache from a JSON file.
pub fn load_cache(path: &Path) -> Result<HashMap<String, Vec<CrateVersionInfo>>> {
    let content =
        std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    serde_json::from_str(&content).context("parsing cache JSON")
}

/// Save the version cache to a JSON file.
pub fn save_cache(path: &Path, cache: &HashMap<String, Vec<CrateVersionInfo>>) -> Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("creating cache directory {}", parent.display()))?;
    }
    let json = serde_json::to_string_pretty(cache)?;
    std::fs::write(path, json).with_context(|| format!("writing cache to {}", path.display()))?;
    Ok(())
}
