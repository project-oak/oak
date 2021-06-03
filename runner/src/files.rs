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

use std::{io::Read, path::PathBuf, process::Command};

pub fn read_file(path: &PathBuf) -> String {
    let mut file = std::fs::File::open(path).expect("could not open file");
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .expect("could not read file contents");
    contents
}

/// Return an iterator of all the first-party and non-ignored files in the repository, which can be
/// then additionally filtered by the caller.
pub fn source_files() -> impl Iterator<Item = PathBuf> {
    let walker = walkdir::WalkDir::new(".").into_iter();
    walker
        .filter_entry(|e| !is_ignored_entry(e))
        .filter_map(Result::ok)
        .map(|e| e.into_path())
}

// TODO: make it a class with the paths
pub fn modified_files() -> Vec<String> {
    let vec = Command::new("git")
        .args(&["status", "--short"])
        .output()
        .expect("could not get modified files")
        .stdout;
    
    // Extract the file names from the git output
    let re = regex::Regex::new(r".{1, 2} (.*)").unwrap();
    String::from_utf8(vec)
        .expect("could not convert to string")
        .split("\n")
        .map(|s| s.trim().to_string())
        .map(|s| {
            re.captures(s.as_str())
                .and_then(|caps| caps.get(1))
                .map_or("", |m| m.as_str())
                .to_string()
        })
        .filter(|s| s.len() > 0)
        .collect()
}

/// Checks if the given file is among the modfied paths
pub fn is_modified(file_path: &str, modified_paths: &Vec<String>) -> bool {
    modified_paths.contains(&file_path.to_string()) || modified_paths.iter().find(|path| file_path.starts_with(path.as_str())).is_some()
}

/// Returns the list of all crates in which at least one file is modified. Returns a list of the paths to the `Cargo.toml` files.
pub fn modified_crates(modified_files: &Vec<String>) -> Vec<String> {
    let mut crates = vec![];
    for path in modified_files {
        if path.ends_with("Cargo.toml") {
            crates.push(path.clone())
        } else if path.ends_with(".rs") {
            // TODO: find and add the Cargo.toml files
        }
    }
    crates
}

pub fn file_contains(path: &PathBuf, pattern: &str) -> bool {
    if path.is_file() {
        let mut file = std::fs::File::open(path).expect("could not open file");
        let mut contents = String::new();
        // Content may be non-UTF-8, in which case we just return false.
        if file.read_to_string(&mut contents).is_ok() {
            contents.contains(pattern)
        } else {
            false
        }
    } else {
        false
    }
}

pub fn example_toml_files() -> impl Iterator<Item = PathBuf> {
    source_files().filter(is_example_toml_file)
}

pub fn fuzz_config_toml_files() -> impl Iterator<Item = PathBuf> {
    source_files().filter(is_fuzz_config_toml_file)
}

/// Return an iterator of all known Cargo Manifest files that define crates.
pub fn crate_manifest_files() -> impl Iterator<Item = PathBuf> {
    source_files()
        .filter(is_cargo_toml_file)
        .filter(|p| is_cargo_package_file(p))
}

/// Return an iterator of all known Cargo Manifest files that define workspaces.
pub fn workspace_manifest_files() -> impl Iterator<Item = PathBuf> {
    source_files()
        .filter(is_cargo_toml_file)
        .filter(|p| is_cargo_workspace_file(p))
}

/// Return whether the provided path refers to a source file in a programming language.
pub fn is_source_code_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".cc")
        || filename.ends_with(".h")
        || filename.ends_with(".rs")
        || filename.ends_with(".proto")
        || filename.ends_with(".js")
        || filename.ends_with(".go")
        || filename.ends_with(".java")
}

/// Return whether the provided path refers to a source file that can be formatted by clang-tidy.
pub fn is_clang_format_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".cc") || filename.ends_with(".h") || filename.ends_with(".proto")
}

/// Return whether the provided path refers to a Bazel file (`BUILD`, `WORKSPACE`, or `*.bzl`)
pub fn is_bazel_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename == "BUILD" || filename == "WORKSPACE" || filename.ends_with(".bzl")
}

pub fn is_build_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename == "BUILD"
}

/// Return whether the provided path refers to a markdown file (`*.md`)
pub fn is_markdown_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".md")
}

pub fn is_dockerfile(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with("Dockerfile")
}

pub fn is_toml_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".toml")
}

pub fn is_yaml_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".yaml") || filename.ends_with(".yml")
}

pub fn is_html_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".htm") || filename.ends_with(".html")
}

pub fn is_javascript_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".js") || filename.ends_with(".mjs")
}

pub fn is_typescript_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".ts") || filename.ends_with(".tsx")
}

pub fn is_shell_script(path: &PathBuf) -> bool {
    if path.is_file() {
        let mut file = std::fs::File::open(path).expect("could not open file");
        let mut contents = String::new();
        match file.read_to_string(&mut contents) {
            Ok(_size) => contents.starts_with("#!"),
            Err(_err) => false,
        }
    } else {
        false
    }
}

/// Return whether the provided path refers to a `fuzz` crate for fuzz testing with `cargo-fuzz`.
pub fn is_fuzzing_toml_file(path: &PathBuf) -> bool {
    format!("{:?}", path).contains("/fuzz/")
}

/// Return whether the provided path refers to a `Cargo.toml` file. Note that it does not
/// differentiate between workspace-level and crate-level files.
fn is_cargo_toml_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename == "Cargo.toml"
}

/// Return whether the provided path refers to a workspace-level `Cargo.toml` file, by looking at
/// the contents of the file.
fn is_cargo_workspace_file(path: &PathBuf) -> bool {
    // We naively look for the `[workspace]` string to appear in the contents of the file. A better
    // alternative would be to actually parse the file as `toml` and figure out whether it has a
    // `workspace` section, but it seems overkill for now.
    file_contains(path, "[workspace]")
}

/// Return whether the provided path refers to a `Cargo.toml` file that defines a crate, by looking
/// at the contents of the file.
fn is_cargo_package_file(path: &PathBuf) -> bool {
    // We naively look for the `[package]` string to appear in the contents of the file. A better
    // alternative would be to actually parse the file as `toml` and figure out whether it has a
    // `package` section, but it seems overkill for now.
    file_contains(path, "[package]")
}

fn is_example_toml_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename == "example.toml"
}

fn is_fuzz_config_toml_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename == "fuzz.toml"
}

fn is_ignored_entry(entry: &walkdir::DirEntry) -> bool {
    let path = entry.clone().into_path();
    // Simple heuristic to try and exclude generated files.
    is_ignored_path(&path) || file_contains(&path, "DO NOT EDIT")
}

/// Return whether to ignore the specified path. This is used by the `walker` package to efficiently
/// avoid descending into blacklisted directories.
fn is_ignored_path(path: &PathBuf) -> bool {
    let components = path.components().collect::<std::collections::HashSet<_>>();
    components.contains(&std::path::Component::Normal(".git".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-cache".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-bin".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-out".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-oak".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-clang-bin".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-clang-out".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-clang-oak".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-client-bin".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-client-out".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-client-oak".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-emscripten-bin".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-emscripten-out".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-emscripten-oak".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-wasm-bin".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-wasm-out".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-wasm-oak".as_ref()))
        || components.contains(&std::path::Component::Normal("cache".as_ref()))
        || components.contains(&std::path::Component::Normal("cargo-cache".as_ref()))
        || components.contains(&std::path::Component::Normal("node_modules".as_ref()))
        || components.contains(&std::path::Component::Normal("protoc_out".as_ref())) // Code generated by protoc
        || components.contains(&std::path::Component::Normal("dist".as_ref())) // Code generated by webpack
        || components.contains(&std::path::Component::Normal("target".as_ref())) // Rust artifacts.
        || components.contains(&std::path::Component::Normal("third_party".as_ref()))
}

pub fn to_string(path: PathBuf) -> String {
    path.to_str().unwrap().to_string()
}
