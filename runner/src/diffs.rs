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

use crate::internal::CargoManifest;
use crate::files::*;

// Get all the files that have been changed in this branch.
pub fn modified_files() -> Vec<String> {
    let vec = Command::new("git")
        .args(&["diff", "--name-only", "HEAD^"])
        .output()
        .expect("could not get modified files")
        .stdout;

    // Extract the file names from the git output
    String::from_utf8(vec)
        .expect("could not convert to string")
        .split('\n')
        .map(|s| format!("./{}", s))
        .collect()
}

/// Checks if the given file is among the modfied paths
pub fn is_modified(file_path: &str, modified_paths: &[String]) -> bool {
    modified_paths.contains(&file_path.to_string())
        || modified_paths
            .iter()
            .any(|path| file_path.starts_with(path.as_str()))
}

/// Returns the list of all crates in which at least one file is modified. Returns a list of the
/// paths to the `Cargo.toml` files.
pub fn directly_modified_crates() -> Vec<String> {
    let modified_files = modified_files();

    let mut crates = hashset![];
    for str_path in modified_files {
        if let Some(crate_path) = find_crate(str_path) {
            crates.insert(crate_path);
        }
    }
    crates.iter().cloned().collect()
}

fn find_crate(str_path: String) -> Option<String> {
    if str_path.ends_with("Cargo.toml") {
        return Some(str_path);
    } else if str_path.ends_with(".rs") {
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

fn affected_protos() -> Vec<String> {
    let mut affected_protos: Vec<String> = modified_files()
        .iter()
        .filter(|p| p.ends_with(".proto"))
        .cloned()
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

fn imported_proto_files(proto_file_path: String) -> Vec<String> {
    let mut imported_protos = vec![];
    if let Ok(file) = std::fs::File::open(proto_file_path) {
        let lines = BufReader::new(file).lines();
        let re = regex::Regex::new(r#"import "(.*)";"#).unwrap();

        for line in lines {
            let line = line.expect("could not read line");
            if let Some(imported) = re.captures(&line).map(|c| c[1].to_string()) {
                imported_protos.push(imported);
            }
        }
    }

    imported_protos
}

/// Path to the `Cargo.toml` file for all crates that are either directly modified or have a
/// dependency to a modified crate.
pub fn all_affected_crates() -> Vec<String> {
    println!("getting affected files");
    let crate_manifest_files = crate_manifest_files();
    println!("got all crate manifest files");
    let mut affected_crates =
        HashSet::<String>::from_iter(directly_modified_crates().iter().cloned());

    let crates_affected_by_protos = crates_affected_by_protos(&affected_protos());
    affected_crates = affected_crates
        .union(&crates_affected_by_protos)
        .cloned()
        .collect();

    for crate_path in crate_manifest_files {
        add_affected_dependencies(crate_path, &mut affected_crates);
    }

    affected_crates.iter().cloned().collect()
}

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
        .map(|build_path| find_crate(build_path).unwrap())
        .collect()
}

fn add_affected_dependencies(crate_path: PathBuf, affected_crates: &mut HashSet<String>) {
    if affected_crates.contains(&to_string(crate_path.clone())) {
        return;
    }
    let deps = get_local_dependencies(&crate_path);
    for dep in deps {
        if !affected_crates.contains(&dep) {
            let dep_path = PathBuf::from(dep.clone());
            add_affected_dependencies(dep_path.clone(), affected_crates)
        }
        if affected_crates.contains(&dep) {
            affected_crates.insert(to_string(crate_path));
            return;
        }
    }
}


/// Get local dependencies.
fn get_local_dependencies(path: &PathBuf) -> Vec<String> {
    let cargo_manifest: CargoManifest = toml::from_str(&read_file(&path))
        .unwrap_or_else(|err| panic!("could not parse crate manifest file {:?}: {}", path, err));

    let mut dependency_paths = vec![];
    cargo_manifest.all_dependency_paths().iter().fold(
        &mut dependency_paths,
        |paths, dep_path_str| {
            let dep_path = PathBuf::from(dep_path_str);
            let dep_path = dep_path.as_path();
            let mut canonical_dep_path = path.clone();
            canonical_dep_path.pop();
            for dir in dep_path.components() {
                if dir == std::path::Component::ParentDir {
                    canonical_dep_path.pop();
                } else {
                    canonical_dep_path.push(dir);
                }
            }
            paths.push(to_string(canonical_dep_path));
            paths
        },
    );

    dependency_paths
}
