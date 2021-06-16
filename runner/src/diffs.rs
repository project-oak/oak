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
    collections::HashSet,
    io::{BufRead, BufReader},
    iter::FromIterator,
    path::PathBuf,
    process::Command,
};

use crate::{
    files::*,
    internal::{CargoManifest, Diffs},
};

#[derive(Debug)]
pub struct ModifiedContent {
    /// List of modified files.
    files: Vec<String>,
    /// If true, acts as if all files are modified or affected.
    all_modified: bool,
}

impl ModifiedContent {
    pub fn contains(&self, file_name: &str) -> bool {
        self.all_modified || self.files.contains(&file_name.to_string())
    }
}

impl IntoIterator for ModifiedContent {
    type Item = String;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.files.into_iter()
    }
}

// Get all the files that have been modified in the commits specified by `diffs`. Does not include
// new files, unless they are added to git. If present, `diffs.commits` must be a positive number.
// If it is zero or negative, only the last commit will be considered for finding the modified
// files. If `diffs.commits` is not present, all files will be considered.
pub fn modified_files(diffs: &Diffs) -> ModifiedContent {
    match diffs.commits {
        None => ModifiedContent {
            files: vec![],
            all_modified: true,
        },
        Some(commits) => {
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
            let files = String::from_utf8(vec)
                .expect("could not convert to string")
                .split('\n')
                .map(|s| format!("./{}", s))
                .collect();
            ModifiedContent {
                files,
                all_modified: false,
            }
        }
    }
}

/// Returns the list of paths to `Cargo.toml` files for all crates in which at least one file is
/// modified.
pub fn directly_modified_crates(diffs: &Diffs) -> ModifiedContent {
    match diffs.commits {
        None => ModifiedContent {
            files: vec![],
            all_modified: true,
        },
        _ => {
            let modified_files = modified_files(diffs);

            let mut crates = hashset![];
            for str_path in modified_files {
                if let Some(crate_path) = find_crate_toml_file(str_path) {
                    crates.insert(crate_path);
                }
            }
            ModifiedContent {
                files: crates.iter().cloned().collect(),
                all_modified: false,
            }
        }
    }
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
fn affected_protos(diffs: &Diffs) -> Vec<String> {
    match diffs.commits {
        None => vec![],
        _ => {
            let mut affected_protos: Vec<String> = modified_files(diffs)
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
        }
    }
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
pub fn all_affected_crates(diffs: &Diffs) -> ModifiedContent {
    match diffs.commits {
        None => ModifiedContent {
            files: vec![],
            all_modified: true,
        },
        _ => {
            let crate_manifest_files = crate_manifest_files();
            let mut affected_crates =
                HashSet::<String>::from_iter(directly_modified_crates(diffs).into_iter());

            let crates_affected_by_protos = crates_affected_by_protos(&affected_protos(diffs));
            affected_crates = affected_crates
                .union(&crates_affected_by_protos)
                .cloned()
                .collect();

            for crate_path in crate_manifest_files {
                add_affected_crates(crate_path, &mut affected_crates);
            }

            ModifiedContent {
                files: affected_crates.iter().cloned().collect(),
                all_modified: false,
            }
        }
    }
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

// Checks if `crate_toml_path` has a direct or indirect dependency to any of the crates in
// `affected_crates_toml_path`. If so, adds `crate_toml_path` and any of its affected dependencies
// to `affected_crates_toml_path`.
fn add_affected_crates(crate_toml_path: PathBuf, affected_crates_toml_path: &mut HashSet<String>) {
    if affected_crates_toml_path.contains(&to_string(crate_toml_path.clone())) {
        return;
    }
    let deps = get_local_dependencies(&crate_toml_path);
    for dep in deps {
        if !affected_crates_toml_path.contains(&dep) {
            let dep_path = PathBuf::from(dep.clone());
            add_affected_crates(dep_path.clone(), affected_crates_toml_path)
        }
        if affected_crates_toml_path.contains(&dep) {
            affected_crates_toml_path.insert(to_string(crate_toml_path));
            return;
        }
    }
}

/// Returns paths to `Cargo.toml` files of local crates (crates belonging to the Oak repo) that the
/// given crate has a dependency to. Converts the relative dependency paths in `Cargo.toml` into
/// paths relative to the repo's root.
fn get_local_dependencies(toml_path: &PathBuf) -> Vec<String> {
    let cargo_manifest: CargoManifest =
        toml::from_str(&read_file(&toml_path)).unwrap_or_else(|err| {
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
            let mut canonical_dep_toml_path = toml_path.clone();
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
