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

//! Parsers for MODULE.bazel (crate specs), MODULE.bazel.lock (resolved
//! versions), and bazel query output (usage counts).

use std::{collections::HashMap, path::Path};

use anyhow::{Context, Result};
use regex::Regex;
use tree_sitter::{Parser, Query, QueryCursor};

use crate::crate_key::CrateKey;

/// Parse MODULE.bazel to extract crate names and their requested versions.
///
/// Uses Starlark native parsing via `tree-sitter` to dynamically evaluate
/// `crate.spec(...)` blocks.
pub fn parse_crate_specs(path: &Path) -> Result<HashMap<String, String>> {
    let content =
        std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;

    // Load the Python/Starlark grammar
    let mut parser = Parser::new();
    let language = tree_sitter_python::language();
    parser.set_language(language).context("error loading python grammar")?;

    // Parse the MODULE.bazel file into a concrete Syntax Tree
    let tree = parser.parse(&content, None).context("failed to parse AST")?;

    // Find all calls where the function is exactly `crate.spec`
    let query_str = r#"
        (call
            function: (attribute
                object: (identifier) @obj
                attribute: (identifier) @method
                (#eq? @obj "crate")
                (#eq? @method "spec")
            )
            arguments: (argument_list) @args
        )
    "#;

    let query = Query::new(language, query_str)?;
    let mut cursor = QueryCursor::new();
    let mut crates = HashMap::new();

    // Iterate through every `crate.spec()` match found in the AST
    for match_ in cursor.matches(&query, tree.root_node(), content.as_bytes()) {
        // Grab the `argument_list` node from our query capture
        let args_node = match_
            .captures
            .iter()
            .find(|c| query.capture_names()[c.index as usize] == "args")
            .unwrap()
            .node;

        let mut package = None;
        let mut version = None;

        // Walk through the parameters (handling commas, newlines, and comments
        // natively)
        let mut walker = args_node.walk();
        for child in args_node.children(&mut walker) {
            if child.kind() == "keyword_argument" {
                // E.g. `package = "serde"`
                let name_node = child.child_by_field_name("name");
                let value_node = child.child_by_field_name("value");

                if let (Some(name), Some(value)) = (name_node, value_node) {
                    let key = name.utf8_text(content.as_bytes())?;
                    // Clean off the python-style quotes
                    let val = value
                        .utf8_text(content.as_bytes())?
                        .trim_matches(|c| c == '"' || c == '\'');

                    match key {
                        "package" => package = Some(val.to_string()),
                        "version" => version = Some(val.to_string()),
                        "git" => version = Some("git".to_string()),
                        _ => {} // Ignore features, optional arguments, etc.
                    }
                }
            }
        }

        // Apply our duplicate dominance logic
        if let (Some(pkg), Some(ver)) = (package, version) {
            let dominated = crates
                .get(&pkg)
                .map(|existing: &String| {
                    parse_version_lenient(existing)
                        .zip(parse_version_lenient(&ver))
                        .map(|(e, v)| v > e)
                        .unwrap_or(false)
                })
                .unwrap_or(true);

            if dominated {
                crates.insert(pkg, ver);
            }
        }
    }

    Ok(crates)
}

/// Parse MODULE.bazel.lock to extract actual installed crate versions.
///
/// Recursively searches the lock JSON for `generatedRepoSpecs` objects and
/// extracts crate names and versions from repo names like
/// `oak_std_crates_index__serde-1.0.210`.
pub fn parse_lock_file(path: &Path) -> Result<HashMap<String, Vec<semver::Version>>> {
    let content =
        std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;

    let lock_data: serde_json::Value =
        serde_json::from_str(&content).context("parsing lock file JSON")?;

    let mut packages: HashMap<String, Vec<semver::Version>> = HashMap::new();

    fn find_repo_specs(value: &serde_json::Value, specs: &mut Vec<serde_json::Value>) {
        match value {
            serde_json::Value::Object(map) => {
                if let Some(repo_specs) = map.get("generatedRepoSpecs") {
                    specs.push(repo_specs.clone());
                }
                for v in map.values() {
                    find_repo_specs(v, specs);
                }
            }
            serde_json::Value::Array(arr) => {
                for item in arr {
                    find_repo_specs(item, specs);
                }
            }
            _ => {}
        }
    }

    let mut all_specs = Vec::new();
    find_repo_specs(&lock_data, &mut all_specs);

    for specs in &all_specs {
        if let serde_json::Value::Object(map) = specs {
            for repo_name in map.keys() {
                if !repo_name.contains("_crates_index__") {
                    continue;
                }
                if let Some(raw_key) = repo_name.split("__").nth(1) {
                    let key = CrateKey::new(raw_key);
                    if let Some(version) = key.semver_version() {
                        packages.entry(key.name().to_string()).or_default().push(version);
                    }
                }
            }
        }
    }

    // Sort and deduplicate each crate's versions
    for versions in packages.values_mut() {
        versions.sort();
        versions.dedup();
    }

    Ok(packages)
}

/// Attempt to parse a version string leniently.
///
/// Strips leading `=`, `^`, `~` prefixes and handles versions missing
/// patch components (e.g. "0.4" → "0.4.0").
pub fn parse_version_lenient(s: &str) -> Option<semver::Version> {
    if s == "*" || s == "git" {
        return None;
    }
    let s = s.trim_start_matches(|c| c == '=' || c == '^' || c == '~');
    // Try direct parse
    if let Ok(v) = semver::Version::parse(s) {
        return Some(v);
    }
    // Try adding .0 for missing patch
    if let Ok(v) = semver::Version::parse(&format!("{}.0", s)) {
        return Some(v);
    }
    // Try adding .0.0 for major-only
    if let Ok(v) = semver::Version::parse(&format!("{}.0.0", s)) {
        return Some(v);
    }
    None
}

/// Strip build metadata (everything after `+`) from a version string.
pub fn strip_metadata(v: &str) -> &str {
    v.split('+').next().unwrap_or(v)
}

/// Get the number of Bazel targets that depend on each crate.
///
/// Runs `bazel query kind('rust_.*', //...) --output build --keep_going`
/// and counts crate references per rule block.
pub fn get_usage_counts() -> HashMap<String, usize> {
    eprintln!("Fetching crate usage counts via bazel query...");

    let result = std::process::Command::new("bazel")
        .args(["query", "kind('rust_.*', //...)", "--output", "build", "--keep_going"])
        .output();

    let output = match result {
        Ok(o) => String::from_utf8_lossy(&o.stdout).to_string(),
        Err(e) => {
            eprintln!("Warning: Failed to get crate usage counts: {}", e);
            return HashMap::new();
        }
    };

    let mut counts: HashMap<String, usize> = HashMap::new();
    let crate_re = Regex::new(r"@oak[a-z_]*_crates_index//:([a-zA-Z0-9_-]+)").expect("valid regex");

    // Each rule in `bazel query --output build` is separated by rule headers.
    for rule_block in output.split("\n# ") {
        let rule_block = rule_block.trim();
        if rule_block.is_empty() {
            continue;
        }
        // Deduplicate crates within a single rule block
        let mut seen = std::collections::HashSet::new();
        for caps in crate_re.captures_iter(rule_block) {
            let crate_name = caps[1].to_string();
            if seen.insert(crate_name.clone()) {
                *counts.entry(crate_name).or_default() += 1;
            }
        }
    }

    counts
}
