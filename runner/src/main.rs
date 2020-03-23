//
// Copyright 2020 The Project Oak Authors
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

//! A utility binary to run tests and orchestrate examples and other tools within the repository,
//! for local development and CI.
//!
//! To invoke, run the following command from the root of the repository:
//!
//! ```
//! cargo run --package=runner
//! ```

use std::io::Read;
use std::path::PathBuf;
use structopt::StructOpt;

mod internal;
use internal::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let opt = Opt::from_args();
    // TODO(#396): Add support for running individual commands via command line flags.
    let root = Step::Multiple {
        name: "root".to_string(),
        steps: vec![
            run_buildifier(),
            run_prettier(),
            run_embedmd(),
            run_cargo_fmt(),
            run_cargo_test(),
            run_cargo_doc_test(),
            run_cargo_clippy(),
            run_bazel_build(),
            run_bazel_test(),
        ],
    };
    let statuses = run_step(&Context::root(&opt), &root);

    // If the overall status value is an error, terminate with a nonzero exit code.
    if statuses.contains(&StatusResultValue::Error) {
        std::process::exit(1);
    }

    Ok(())
}

/// Return whether to ignore the specified path. This is used by the `walker` package to efficiently
/// avoid descending into blacklisted directories.
fn is_ignored_path(path: &PathBuf) -> bool {
    path.starts_with("./bazel-cache")
        || path.starts_with("./bazel-clang-oak")
        || path.starts_with("./bazel-client-oak")
        || path.starts_with("./bazel-oak")
        || path.starts_with("./cargo-cache")
        || path.starts_with("./third_party")
        || path.starts_with("./.git")
        || path.ends_with("target") // Rust artifacts.
}

fn is_ignored_entry(entry: &walkdir::DirEntry) -> bool {
    let path = entry.clone().into_path();
    is_ignored_path(&path)
}

/// Return an iterator of all the first-party and non-ignored files in the repository, which can be
/// then additionally filtered by the caller.
fn source_files() -> impl Iterator<Item = PathBuf> {
    let walker = walkdir::WalkDir::new(".").into_iter();
    walker
        .filter_entry(|e| !is_ignored_entry(e))
        .filter_map(Result::ok)
        .map(|e| e.into_path())
}

/// Return an iterator of all known Cargo Manifest files that define workspaces.
fn workspace_manifest_files() -> impl Iterator<Item = PathBuf> {
    source_files()
        .filter(is_cargo_toml_file)
        .filter(is_cargo_workspace_file)
}

/// Return whether the provided path refers to a Bazel file (`BUILD`, `WORKSPACE`, or `*.bzl`)
fn is_bazel_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename == "BUILD" || filename == "WORKSPACE" || filename.ends_with(".bzl")
}

/// Return whether the provided path refers to a markdown file (`*.md`)
fn is_markdown_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".md")
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
    let mut file = std::fs::File::open(path).expect("could not open file");
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .expect("could not read file contents");
    // We naively look for the `[workspace]` string to appear in the contents of the file. A better
    // alternative would be to actually parse the file as `toml` and figure out whether it has a
    // `workspace` section, but it seems overkill for now.
    contents.contains("[workspace]")
}

fn run_buildifier() -> Step {
    Step::Multiple {
        name: "buildifier".to_string(),
        steps: source_files()
            .filter(is_bazel_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                runnable: cmd("buildifier", &["-lint=warn", "-mode=check", &entry]),
            })
            .collect(),
    }
}

fn run_prettier() -> Step {
    Step::Multiple {
        name: "prettier".to_string(),
        steps: source_files()
            .filter(is_markdown_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                runnable: cmd("prettier", &["--check", &entry]),
            })
            .collect(),
    }
}

fn run_embedmd() -> Step {
    Step::Multiple {
        name: "embedmd".to_string(),
        steps: source_files()
            .filter(is_markdown_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                runnable: cmd("embedmd", &["-d", &entry]),
            })
            .collect(),
    }
}

fn run_cargo_fmt() -> Step {
    Step::Multiple {
        name: "cargo fmt".to_string(),
        steps: workspace_manifest_files()
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                runnable: cmd(
                    "cargo",
                    &[
                        "fmt",
                        "--all",
                        &format!("--manifest-path={}", &entry),
                        "--",
                        "--check",
                    ],
                ),
            })
            .collect(),
    }
}

fn run_cargo_test() -> Step {
    Step::Multiple {
        name: "cargo test".to_string(),
        steps: workspace_manifest_files()
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                runnable: cmd(
                    "cargo",
                    &[
                        "test",
                        "--all-targets",
                        &format!("--manifest-path={}", &entry),
                    ],
                ),
            })
            .collect(),
    }
}

fn run_cargo_doc_test() -> Step {
    Step::Multiple {
        name: "cargo doc test".to_string(),
        steps: workspace_manifest_files()
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                runnable: cmd(
                    "cargo",
                    &["test", "--doc", &format!("--manifest-path={}", &entry)],
                ),
            })
            .collect(),
    }
}

fn run_cargo_clippy() -> Step {
    Step::Multiple {
        name: "cargo clippy".to_string(),
        steps: workspace_manifest_files()
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                runnable: cmd(
                    "cargo",
                    &[
                        "clippy",
                        "--all-targets",
                        &format!("--manifest-path={}", &entry),
                        "--",
                        "--deny=warnings",
                    ],
                ),
            })
            .collect(),
    }
}

fn run_bazel_build() -> Step {
    Step::Single {
        name: "bazel build".to_string(),
        runnable: cmd("bazel", &["build", "--", "//oak/...:all"]),
    }
}

fn run_bazel_test() -> Step {
    Step::Single {
        name: "bazel test".to_string(),
        runnable: cmd(
            "bazel",
            // TODO(#396): Extract these targets with `bazel query` at runtime,
            // based on some label or attribute.
            &[
                "test",
                "//oak/server:host_tests",
                "//oak/server/storage:host_tests",
                "//oak/common:host_tests",
            ],
        ),
    }
}

pub fn to_string(path: PathBuf) -> String {
    path.to_str().unwrap().to_string()
}
