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

//! Dependency graph extraction and reverse-dependency path tracing.
//!
//! Parses `MODULE.bazel.lock` to build a crate dependency graph, then walks
//! it backwards to show why a particular crate is included and what depends
//! on it.

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    io::{self, Write},
    path::Path,
};

use anyhow::{Context, Result};
use colored::Colorize;
use regex::Regex;

use crate::crate_key::CrateKey;

/// Maps each crate key to the set of crate keys it is connected to.
type AdjacencyMap = HashMap<CrateKey, HashSet<CrateKey>>;

/// Dependency graph extracted from MODULE.bazel.lock.
pub struct DepGraph {
    /// crate_key → set of crate_keys it depends on.
    forward: AdjacencyMap,
    /// crate_key → set of crate_keys that depend on it.
    reverse: AdjacencyMap,
}

impl DepGraph {
    /// Build a dependency graph from MODULE.bazel.lock.
    ///
    /// Walks all `generatedRepoSpecs` entries, extracts dep labels from the
    /// embedded BUILD.bazel content, and builds forward + reverse adjacency
    /// maps. Crate indexes (`oak_std_crates_index`, `oak_no_std_crates_index`,
    /// etc.) are merged into a single graph.
    pub fn from_lock_file(path: &Path) -> Result<Self> {
        let content =
            std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
        let data: serde_json::Value =
            serde_json::from_str(&content).context("parsing lock file JSON")?;

        let mut forward: AdjacencyMap = HashMap::new();
        let mut reverse: AdjacencyMap = HashMap::new();

        // Matches dep labels like @oak_std_crates_index__serde-1.0.228//:serde
        let dep_re = Regex::new(r"@oak_\w+_crates_index__([^/]+)//").expect("valid regex");

        let mut all_specs = Vec::new();
        find_generated_repo_specs(&data, &mut all_specs);

        for specs in &all_specs {
            if let serde_json::Value::Object(map) = specs {
                for (repo_name, spec) in map {
                    if !repo_name.contains("_crates_index__") {
                        continue;
                    }
                    let crate_key = match repo_name.split("__").nth(1) {
                        Some(k) => CrateKey::new(k),
                        None => continue,
                    };

                    // Try contents["BUILD.bazel"], fall back to build_file_content
                    let build_content = spec.get("attributes").and_then(|a| {
                        a.get("contents")
                            .and_then(|c| c.get("BUILD.bazel"))
                            .and_then(|b| b.as_str())
                            .or_else(|| a.get("build_file_content").and_then(|b| b.as_str()))
                    });

                    if let Some(build_str) = build_content {
                        let deps: HashSet<CrateKey> = dep_re
                            .captures_iter(build_str)
                            .map(|cap| CrateKey::new(&cap[1]))
                            .filter(|dep| *dep != crate_key)
                            .collect();

                        for dep in &deps {
                            reverse.entry(dep.clone()).or_default().insert(crate_key.clone());
                        }

                        forward.insert(crate_key, deps);
                    } else {
                        forward.entry(crate_key).or_default();
                    }
                }
            }
        }

        Ok(DepGraph { forward, reverse })
    }

    /// Find all crate keys matching the given crate name.
    fn find_keys(&self, name: &str) -> Vec<CrateKey> {
        let mut keys: BTreeSet<CrateKey> = BTreeSet::new();
        for key in self.forward.keys().chain(self.reverse.keys()) {
            if key.name() == name {
                keys.insert(key.clone());
            }
        }
        keys.into_iter().collect()
    }

    /// Get all unique crate names in the graph.
    fn all_crate_names(&self) -> Vec<String> {
        let mut names: BTreeSet<String> = BTreeSet::new();
        for key in self.forward.keys().chain(self.reverse.keys()) {
            names.insert(key.name().to_string());
        }
        names.into_iter().collect()
    }

    /// Print dependency info for a crate, showing dependents (reverse),
    /// dependencies (forward), and all paths from root crates.
    pub fn print_deps(&self, crate_name: &str, depth: usize) -> io::Result<()> {
        let out = io::stdout();
        let mut out = out.lock();

        let keys = self.find_keys(crate_name);

        if keys.is_empty() {
            writeln!(out, "No crate matching \"{}\" found in lock file.", crate_name)?;
            let suggestions: Vec<_> =
                self.all_crate_names().into_iter().filter(|n| n.contains(crate_name)).collect();
            if !suggestions.is_empty() {
                writeln!(out, "Did you mean: {}", suggestions.join(", "))?;
            }
            return Ok(());
        }

        writeln!(
            out,
            "{}",
            format!(
                "Dependency info for \"{}\" ({} version{} in lock file):\n",
                crate_name,
                keys.len(),
                if keys.len() == 1 { "" } else { "s" }
            )
            .bold()
        )?;

        for key in &keys {
            let version = key.version();
            let fwd_count = self.forward.get(key).map(|s| s.len()).unwrap_or(0);
            let rev_count = self.reverse.get(key).map(|s| s.len()).unwrap_or(0);

            writeln!(
                out,
                "  {} {} ({} dependents, {} dependencies)",
                crate_name.bold(),
                version.bright_cyan(),
                rev_count,
                fwd_count,
            )?;

            // --- Dependents (reverse tree: who depends on this?) ---
            writeln!(out)?;
            writeln!(out, "    {}", "Depended on by:".bold().underline())?;
            if rev_count > 0 {
                self.print_reverse_tree(&mut out, key, depth, 6, &mut HashSet::new())?;
            } else {
                writeln!(out, "      {}", "(no crates depend on this)".dimmed())?;
            }

            // --- Dependencies (forward tree: what does this pull in?) ---
            writeln!(out)?;
            writeln!(out, "    {}", "Depends on:".bold().underline())?;
            if fwd_count > 0 {
                self.print_forward_tree(&mut out, key, depth, 6, &mut HashSet::new())?;
            } else {
                writeln!(out, "      {}", "(no dependencies)".dimmed())?;
            }

            // --- Paths from roots ---
            writeln!(out)?;
            writeln!(out, "    {}", "Paths from root crates:".bold().underline())?;
            let mut paths = Vec::new();
            self.find_paths_to_roots(key, &mut vec![key.clone()], &mut paths, depth + 5);
            if paths.is_empty() {
                writeln!(out, "      {}", "(this is a root crate)".dimmed())?;
            } else {
                self.print_root_paths(&mut out, &paths)?;
            }

            writeln!(out)?;
        }

        Ok(())
    }

    /// Recursively print the reverse dependency tree.
    ///
    /// For each crate that depends on `key`, prints it with an arrow and
    /// recurses up to `depth` levels. Tracks visited nodes per-path to
    /// detect cycles without suppressing legitimate repeated appearances
    /// in different branches.
    fn print_reverse_tree(
        &self,
        out: &mut impl Write,
        key: &CrateKey,
        depth: usize,
        indent: usize,
        visited: &mut HashSet<CrateKey>,
    ) -> io::Result<()> {
        if depth == 0 {
            return Ok(());
        }

        if let Some(rev_deps) = self.reverse.get(key) {
            let mut sorted: Vec<_> = rev_deps.iter().collect();
            sorted.sort();

            for dep_key in sorted {
                let (name, version) = (dep_key.name(), dep_key.version());
                let is_cycle = !visited.insert(dep_key.clone());

                write!(out, "{:indent$}{} ", "", "←".bright_yellow(), indent = indent)?;
                write!(out, "{} {}", name, version.bright_cyan())?;
                if is_cycle {
                    write!(out, " {}", "(cycle)".dimmed())?;
                }
                writeln!(out)?;

                if !is_cycle && depth > 1 {
                    self.print_reverse_tree(out, dep_key, depth - 1, indent + 2, visited)?;
                }

                visited.remove(dep_key);
            }
        }

        Ok(())
    }

    /// Recursively print the forward dependency tree.
    ///
    /// For each crate that `key` depends on, prints it with an arrow and
    /// recurses up to `depth` levels.
    fn print_forward_tree(
        &self,
        out: &mut impl Write,
        key: &CrateKey,
        depth: usize,
        indent: usize,
        visited: &mut HashSet<CrateKey>,
    ) -> io::Result<()> {
        if depth == 0 {
            return Ok(());
        }

        if let Some(fwd_deps) = self.forward.get(key) {
            let mut sorted: Vec<_> = fwd_deps.iter().collect();
            sorted.sort();

            for dep_key in sorted {
                let (name, version) = (dep_key.name(), dep_key.version());
                let is_cycle = !visited.insert(dep_key.clone());

                write!(out, "{:indent$}{} ", "", "→".bright_green(), indent = indent)?;
                write!(out, "{} {}", name, version.bright_cyan())?;
                if is_cycle {
                    write!(out, " {}", "(cycle)".dimmed())?;
                }
                writeln!(out)?;

                if !is_cycle && depth > 1 {
                    self.print_forward_tree(out, dep_key, depth - 1, indent + 2, visited)?;
                }

                visited.remove(dep_key);
            }
        }

        Ok(())
    }

    /// Walk reverse edges to find all paths from root crates (crates with no
    /// reverse dependencies) down to the target. Each path is stored as a
    /// vec of crate keys from root → target.
    fn find_paths_to_roots(
        &self,
        key: &CrateKey,
        current_path: &mut Vec<CrateKey>,
        all_paths: &mut Vec<Vec<CrateKey>>,
        max_depth: usize,
    ) {
        if current_path.len() > max_depth {
            return;
        }

        // Cap total collected paths to prevent combinatorial explosion.
        const MAX_PATHS: usize = 50;
        if all_paths.len() >= MAX_PATHS {
            return;
        }

        let rev_deps = self.reverse.get(key);
        let is_root = rev_deps.is_none() || rev_deps.is_some_and(|deps| deps.is_empty());

        if is_root {
            // Reverse to get root → target order.
            let mut path = current_path.clone();
            path.reverse();
            all_paths.push(path);
            return;
        }

        if let Some(deps) = rev_deps {
            let mut sorted: Vec<_> = deps.iter().collect();
            sorted.sort();

            for dep_key in sorted {
                // Cycle detection within a single path.
                if current_path.contains(dep_key) {
                    continue;
                }
                current_path.push(dep_key.clone());
                self.find_paths_to_roots(dep_key, current_path, all_paths, max_depth);
                current_path.pop();
            }
        }
    }

    /// Pretty-print paths from root crates to the target.
    fn print_root_paths(&self, out: &mut impl Write, paths: &[Vec<CrateKey>]) -> io::Result<()> {
        for (i, path) in paths.iter().enumerate() {
            write!(out, "      ")?;
            for (j, key) in path.iter().enumerate() {
                let (name, version) = (key.name(), key.version());
                if j > 0 {
                    write!(out, " {} ", "→".dimmed())?;
                }
                // Highlight the last element (the target).
                if j == path.len() - 1 {
                    write!(out, "{}", name.bold())?;
                } else {
                    write!(out, "{}", name)?;
                }
                if !version.is_empty() {
                    write!(out, " {}", version.bright_cyan())?;
                }
            }
            writeln!(out)?;

            // If there are too many paths, indicate truncation.
            if i == 49 {
                writeln!(
                    out,
                    "      {}",
                    format!("... and more (showing first {} paths)", i + 1).dimmed()
                )?;
                break;
            }
        }
        Ok(())
    }
}

/// Recursively find all `generatedRepoSpecs` values in the JSON tree.
fn find_generated_repo_specs(value: &serde_json::Value, specs: &mut Vec<serde_json::Value>) {
    match value {
        serde_json::Value::Object(map) => {
            if let Some(repo_specs) = map.get("generatedRepoSpecs") {
                specs.push(repo_specs.clone());
            }
            for v in map.values() {
                find_generated_repo_specs(v, specs);
            }
        }
        serde_json::Value::Array(arr) => {
            for item in arr {
                find_generated_repo_specs(item, specs);
            }
        }
        _ => {}
    }
}
