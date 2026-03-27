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

mod crate_key;
mod crates_io;
mod deps;
mod parse;
mod report;

use std::{collections::HashMap, io::Write, path::PathBuf};

use anyhow::{Context, Result};
use clap::Parser;

use crate::{
    crates_io::{fetch_crate_versions, load_cache, save_cache},
    parse::{get_usage_counts, parse_crate_specs, parse_lock_file},
    report::print_report,
};

/// Version metadata for a single release of a crate on crates.io.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CrateVersionInfo {
    /// The semantic version string (e.g., "1.0.5").
    pub version: String,
    /// Whether this specific version has been yanked from crates.io.
    pub yanked: bool,
    /// The timestamp when this version was published (e.g.,
    /// "2023-11-20T15:30:00Z").
    pub created_at: String,
}

/// All collected data and analysis results for a single crate dependency.
pub struct CrateData {
    /// The name of the crate (e.g., "serde").
    pub name: String,
    /// The exact version requirement specified in the Bazel configuration.
    pub requested: String,
    /// The list of actual, resolved versions present in the `Cargo.lock` /
    /// `MODULE.bazel.lock`. There can be multiple versions if different
    /// dependencies require different versions.
    pub actual: Vec<semver::Version>,
    /// A list of all published releases of this crate retrieved from crates.io.
    pub versions: Vec<CrateVersionInfo>,
    /// The number of times this crate is referenced across internal `BUILD`
    /// targets.
    pub usage: usize,
}

#[derive(Parser)]
#[command(name = "analyze_crate_versions")]
#[command(about = "Analyze crate versions by comparing requested versions in Bazel config, \
    actual versions in the lockfile, and the latest versions on crates.io.")]
#[command(after_help = "\
Report columns:
  Latest(P): Highest available Patch update.
  Latest(m): Highest available Minor update.
  Latest(M): Highest available Major update.

A dash (-) indicates that no update of that type is available \
(e.g., you are already on the latest patch).")]
#[command(term_width = 80)]
struct Cli {
    /// Path to MODULE.bazel.lock
    #[arg(default_value = "MODULE.bazel.lock")]
    lock_file: PathBuf,

    /// Path to MODULE.bazel.
    #[arg(long, default_value = "MODULE.bazel")]
    bzl_file: PathBuf,

    /// Path to a custom versions cache file.
    #[arg(long, default_value_os_t = default_cache_path())]
    versions_file: PathBuf,

    /// Force update the versions cache from crates.io.
    ///
    /// This will fetch the latest data even if a cache file already exists
    /// locally.
    #[arg(short, long)]
    update: bool,

    /// Filter report by crate name (substring match)
    #[arg(short, long)]
    filter: Option<String>,

    /// Include pre-release versions in the report
    #[arg(long)]
    include_pre_release: bool,

    /// Show dependency paths for a specific crate
    #[arg(long)]
    deps: Option<String>,

    /// Depth of reverse-dependency tree (used with --deps)
    #[arg(long, default_value = "1", requires = "deps")]
    depth: usize,
}

fn default_cache_path() -> PathBuf {
    let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
    PathBuf::from(home).join(".cache").join("oak").join("crate_cache.json")
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    // --deps mode: build dep graph and print, then exit.
    if let Some(ref crate_name) = cli.deps {
        anyhow::ensure!(cli.lock_file.exists(), "{} not found", cli.lock_file.display());
        eprintln!("Building dependency graph from {}...", cli.lock_file.display());
        let dep_graph = deps::DepGraph::from_lock_file(&cli.lock_file)?;
        dep_graph.print_deps(crate_name, cli.depth)?;
        return Ok(());
    }

    let bzl_file = cli.bzl_file;
    let versions_path = cli.versions_file;

    // Validate inputs
    anyhow::ensure!(bzl_file.exists(), "{} not found", bzl_file.display());
    anyhow::ensure!(cli.lock_file.exists(), "{} not found", cli.lock_file.display());

    // Load cache
    let (cached_versions, cache_age) = if versions_path.exists() && !cli.update {
        let age = versions_path.metadata()?.modified()?.elapsed().unwrap_or_default();
        let cache = load_cache(&versions_path)
            .with_context(|| format!("Failed to load cache from {}", versions_path.display()))?;
        (cache, Some(age))
    } else {
        if cli.update {
            eprintln!(
                "Forcing update of versions from crates.io to {}...",
                versions_path.display()
            );
        } else {
            eprintln!(
                "Versions cache {} not found. Fetching from crates.io...",
                versions_path.display()
            );
        }
        (HashMap::new(), None)
    };

    // Parse sources
    let requested_crates = parse_crate_specs(&bzl_file)?;
    let actual_crates = parse_lock_file(&cli.lock_file)?;
    let usage_counts = get_usage_counts();

    // Determine if we need a full fetch (cache miss or forced update)
    let need_full_fetch = !versions_path.exists() || cli.update;
    let collect_filter = if need_full_fetch { None } else { cli.filter.as_deref() };

    // Build sorted crate name list, optionally filtered
    let mut crate_names: Vec<&String> = requested_crates.keys().collect();
    crate_names.sort();

    if let Some(f) = collect_filter {
        let f_lower = f.to_lowercase();
        crate_names.retain(|n| n.to_lowercase().contains(&f_lower));
    }

    let total = crate_names.len();
    let mut data = Vec::new();
    let mut fetched_any = false;
    let mut all_versions_cache = cached_versions;

    for (i, name) in crate_names.iter().enumerate() {
        let requested = requested_crates[*name].clone();
        let actual = actual_crates.get(*name).cloned().unwrap_or_default();
        let usage = usage_counts.get(name.as_str()).copied().unwrap_or(0);

        let versions = if let Some(cached) = all_versions_cache.get(*name) {
            cached.clone()
        } else {
            fetched_any = true;
            eprint!("\r[{}/{}] Fetching versions for {}...", i + 1, total, name);
            let _ = std::io::stderr().flush();
            let v = fetch_crate_versions(name).unwrap_or_else(|e| {
                eprintln!("\nWarning: Failed to fetch {}: {}", name, e);
                Vec::new()
            });
            // Be nice to crates.io
            std::thread::sleep(std::time::Duration::from_millis(50));
            // Cache what we fetched
            all_versions_cache.insert(name.to_string(), v.clone());
            v
        };

        data.push(CrateData { name: name.to_string(), requested, actual, versions, usage });
    }

    if fetched_any {
        eprintln!("\nFinished fetching data for {} crates.", total);
    }

    // Save cache if we did a full fetch
    if need_full_fetch {
        save_cache(&versions_path, &all_versions_cache)?;
    }

    // Apply filter for report (may differ from collection filter for full fetches)
    let total_count = data.len();
    let report_data: Vec<&CrateData> = if let Some(ref f) = cli.filter {
        let f_lower = f.to_lowercase();
        data.iter().filter(|d| d.name.to_lowercase().contains(&f_lower)).collect()
    } else {
        data.iter().collect()
    };

    print_report(
        &report_data,
        total_count,
        cli.include_pre_release,
        Some(&versions_path),
        cache_age.map(|d| d.as_secs()),
    )?;

    Ok(())
}
