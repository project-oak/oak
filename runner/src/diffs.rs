//
// Copyright 2021 The Project Oak Authors
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

use maplit::hashset;
use std::{
    collections::{HashMap, HashSet},
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
    process::Command,
};

use crate::{
    files::*,
    internal::{CargoManifest, Commits},
};

#[derive(Debug)]
pub struct ModifiedContent {
    /// List of modified files.
    pub files: Option<Vec<String>>,
}

impl ModifiedContent {
    pub fn contains(&self, file_name: &str) -> bool {
        self.files.is_none()
            || self
                .files
                .as_ref()
                .unwrap()
                .contains(&file_name.to_string())
    }
}

// Get all the files that have been modified in the commits specified by `commits`. Does not include
// new files, unless they are added to git. If present, `commits.commits` must be a positive number.
// If it is zero or negative, only the last commit will be considered for finding the modified
// files. If `commits.commits` is not present, all files will be considered.
pub fn modified_files(commits: &Commits) -> ModifiedContent {
    let files = commits.commits.map(|commits| {
        let vec = Command::new("git")
            .args(&[
                "diff",
                "--name-only",
                &format!("HEAD~{}", std::cmp::max(1, commits)),
            ])
            .output()
            .expect("could not get modified files")
            .stdout;

        // Extract the file names from the git output
        String::from_utf8(vec)
            .expect("could not convert to string")
            .split('\n')
            .map(|s| format!("./{}", s))
            .collect()
    });
    ModifiedContent { files }
}

/// Returns the list of paths to `Cargo.toml` files for all crates in which at least one file is
/// modified.
pub fn directly_modified_crates(commits: &Commits) -> ModifiedContent {
    let files = modified_files(commits).files.map(|modified_files| {
        let mut crates = hashset![];
        for str_path in modified_files {
            if let Some(crate_path) = find_crate_toml_file(str_path) {
                crates.insert(crate_path);
            }
        }
        crates.iter().cloned().collect()
    });
    ModifiedContent { files }
}

fn find_crate_toml_file(str_path: String) -> Option<String> {
    if str_path.ends_with("Cargo.toml") {
        return Some(str_path);
    } else if str_path.ends_with(".rs") || str_path.ends_with(".lock") {
        let mut path = PathBuf::from(&str_path);
        while path.parent().is_some() {
            path.pop();
            let crate_path = path.join("Cargo.toml");
            let crate_path = crate_path.as_path();
            if crate_path.exists() {
                return Some(crate_path.to_str().unwrap().to_string());
            }
        }
    }
    None
}

/// List of paths to all `.proto` files affected by the recent changes.
fn affected_protos(commits: &Commits) -> Vec<String> {
    modified_files(commits)
        .files
        .map(|modified_files| {
            let mut affected_protos: Vec<String> = modified_files
                .into_iter()
                .filter(|p| p.ends_with(".proto"))
                .collect();

            if !affected_protos.is_empty() {
                let all_protos = source_files()
                    .map(to_string)
                    .map(|s| s.replace("./", ""))
                    .filter(|p| p.ends_with(".proto"));

                for proto in all_protos {
                    add_affected_protos(proto, &mut affected_protos);
                }
            }

            affected_protos
        })
        .unwrap_or_else(Vec::new)
}

/// Adds `proto_path` to the list of `affected_protos` if `proto_path` or any of its imported protos
/// imports any of the proto files in `affected_protos`.
fn add_affected_protos(proto_path: String, affected_protos: &mut Vec<String>) {
    if affected_protos.contains(&proto_path) {
        return;
    }

    let imported_proto_files = imported_proto_files(proto_path.clone());
    for imported_proto_file in imported_proto_files {
        if !affected_protos.contains(&imported_proto_file) {
            add_affected_protos(imported_proto_file.clone(), affected_protos);
        }

        if affected_protos.contains(&imported_proto_file) {
            affected_protos.push(proto_path);
            return;
        }
    }
}

/// Returns paths to all `.proto` files that `proto_file_path` imports.
fn imported_proto_files(proto_file_path: String) -> Vec<String> {
    let mut imported_protos = vec![];
    if let Ok(file) = std::fs::File::open(proto_file_path) {
        let lines = BufReader::new(file).lines();
        let re = regex::Regex::new(r#"import "(.*)";"#).unwrap();

        // Scan the lines in the file line by line to find all the imports.
        for line in lines {
            let line = line.expect("could not read line");
            if let Some(imported) = re.captures(&line).map(|c| c[1].to_string()) {
                imported_protos.push(imported);
            }
        }
    }

    imported_protos
}

/// Path to the `Cargo.toml` files for all crates that are either directly modified or have a
/// dependency to a modified crate.
pub fn all_affected_crates(commits: &Commits) -> ModifiedContent {
    let files = directly_modified_crates(commits)
        .files
        .map(|modified_files| {
            let crate_manifest_files = crate_manifest_files();
            // A map of `Cargo.toml` files visited by the algorithm. If the value associated with a
            // key is `true`, the crate is affected by the changes and should be included in the
            // result.
            let mut affected_crates: HashMap<String, bool> = modified_files
                .into_iter()
                .map(|path| (path, true))
                .collect();

            crates_affected_by_protos(&affected_protos(commits))
                .iter()
                .fold(&mut affected_crates, |affected_crates, toml_path| {
                    affected_crates.insert(toml_path.clone(), true);
                    affected_crates
                });

            for crate_path in crate_manifest_files {
                add_affected_crates(crate_path, &mut affected_crates);
            }

            // Return `Cargo.toml` files of the crates that are affected by the changes
            affected_crates
                .iter()
                .filter(|(_key, value)| **value)
                .map(|(key, _value)| key.clone())
                .collect()
        });

    ModifiedContent { files }
}

/// Returns the paths to `Cargo.toml` files of crates affected by the changed proto files.
fn crates_affected_by_protos(affected_protos: &[String]) -> HashSet<String> {
    source_files()
        .filter(|path| to_string(path.clone()).ends_with("build.rs"))
        .filter(|path| {
            for proto in affected_protos {
                if file_contains(path, proto) {
                    return true;
                }
            }
            false
        })
        .map(to_string)
        .map(|build_path| find_crate_toml_file(build_path).unwrap())
        .collect()
}

/// Checks if `crate_toml_path` has a direct or indirect dependency to any of the affected crates in
/// `affected_crates_toml_path`. If so, adds `crate_toml_path` and any of its affected dependencies
/// to `affected_crates_toml_path`.
///
/// Keys in `affected_crates_toml_path` are paths to visited `Cargo.toml` files. If the value
/// associated with a key is `true`, then the corresponding crate is affected by the changes.
fn add_affected_crates(
    crate_toml_path: PathBuf,
    affected_crates_toml_path: &mut HashMap<String, bool>,
) {
    // Return immediately, if the `crate_toml_path` is already visited.
    if affected_crates_toml_path.contains_key(&to_string(crate_toml_path.clone())) {
        return;
    }
    let deps = get_local_dependencies(&crate_toml_path);
    for dep in deps {
        // If the dependency is not visited, visit it and its dependencies
        if !affected_crates_toml_path.contains_key(&dep) {
            let dep_path = PathBuf::from(dep.clone());
            add_affected_crates(dep_path.clone(), affected_crates_toml_path)
        }
        if *affected_crates_toml_path.get(&dep).unwrap_or(&false) {
            affected_crates_toml_path.insert(to_string(crate_toml_path), true);
            return;
        }
    }
    affected_crates_toml_path.insert(to_string(crate_toml_path), false);
}

/// Returns paths to `Cargo.toml` files of local crates (crates belonging to the Oak repo) that the
/// given crate has a dependency to. Converts the relative dependency paths in `Cargo.toml` into
/// paths relative to the repo's root.
fn get_local_dependencies(toml_path: &Path) -> Vec<String> {
    let cargo_manifest: CargoManifest =
        toml::from_str(&read_file(toml_path)).unwrap_or_else(|err| {
            panic!(
                "could not parse crate manifest file {:?}: {}",
                toml_path, err
            )
        });

    let mut dependency_toml_paths = vec![];
    cargo_manifest
        .all_dependencies_with_toml_path()
        .iter()
        .fold(&mut dependency_toml_paths, |paths, dep_path_str| {
            let dep_path = PathBuf::from(dep_path_str);
            let dep_path = dep_path.as_path();
            let mut canonical_dep_toml_path = toml_path.to_path_buf();
            canonical_dep_toml_path.pop();
            // Change the path to be relative to the repo's root.
            for dir in dep_path.components() {
                if dir == std::path::Component::ParentDir {
                    canonical_dep_toml_path.pop();
                } else {
                    canonical_dep_toml_path.push(dir);
                }
            }
            paths.push(to_string(canonical_dep_toml_path));
            paths
        });

    dependency_toml_paths
}
