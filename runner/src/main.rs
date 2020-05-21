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

use std::{
    io::Read,
    path::{Path, PathBuf},
};
use structopt::StructOpt;

mod internal;
use internal::*;
mod todo_check;
use todo_check::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let opt = Opt::from_args();

    let steps = match opt.cmd {
        Command::BuildExamples(ref opt) => build_examples(&opt),
        Command::RunExamples(ref opt) => run_examples(&opt),
        Command::BuildServer(ref opt) => build_server(&opt),
        Command::RunTests => run_tests(),
    };
    // TODO(#396): Add support for running individual commands via command line flags.
    let statuses = run_step(&Context::root(&opt), &steps);

    // If the overall status value is an error, terminate with a nonzero exit code.
    if statuses.contains(&StatusResultValue::Error) {
        std::process::exit(1);
    }

    Ok(())
}

fn build_examples(opt: &BuildExamples) -> Step {
    match opt.application_variant.as_str() {
        "rust" => Step::Multiple {
            name: "root".to_string(),
            steps: examples()
                .filter(is_cargo_toml_file)
                .filter(|entry| {
                    // Exclude Cargo.toml files of targets that are not meant to be compiled to
                    // Wasm (e.g. auxiliary binaries).
                    (*entry != PathBuf::from("./examples/aggregator/backend/Cargo.toml"))
                        && (*entry != PathBuf::from("./examples/authentication/server/Cargo.toml"))
                        && (*entry != PathBuf::from("./examples/authentication/client/Cargo.toml"))
                })
                .map(to_string)
                .map(|entry| build_wasm_module(&entry))
                .collect(),
        },
        "cpp" => unimplemented!("C++ examples not implemented yet"),
        v => panic!("unknown variant: {}", v),
    }
}

fn run_examples(opt: &RunExamples) -> Step {
    match opt.application_variant.as_str() {
        "rust" => Step::Multiple {
            name: "examples".to_string(),
            /// TODO(#396): Check that all the example folders are covered by an entry here, or
            /// explicitly ignored. This will probably require pulling out the `Vec<Example>` to a
            /// top-level method first.
            steps: vec![
                Example {
                    name: "abitest".to_string(),
                    rust_module_names: vec!["module_0".to_string(), "module_1".to_string()],
                    // TODO(#730): reinstate Roughtime tests when Rust runtime supports them.
                    // TODO(#1040): reinstate storage tests when Rust runtime supports them.
                    // TODO(#953): reinstate gRPC server server-streaming tests when Rust runtime
                    // supports them.
                    additional_client_flags: vec![
                        "--cert_chain=../../../../../../../../examples/certs/local/local.pem"
                            .to_string(),
                        "--private_key=../../../../../../../../examples/certs/local/local.key"
                            .to_string(),
                        "--test_exclude=(Roughtime|Storage|GrpcServerServerStreamingMethod)"
                            .to_string(),
                    ],
                },
                Example {
                    name: "aggregator".to_string(),
                    rust_module_names: vec!["module".to_string()],
                    additional_client_flags: vec![],
                },
                Example {
                    name: "hello_world".to_string(),
                    rust_module_names: vec!["module".to_string()],
                    additional_client_flags: vec![],
                },
                Example {
                    name: "machine_learning".to_string(),
                    rust_module_names: vec!["module".to_string()],
                    additional_client_flags: vec![],
                },
                Example {
                    name: "private_set_intersection".to_string(),
                    rust_module_names: vec!["module".to_string()],
                    additional_client_flags: vec![],
                },
                Example {
                    name: "running_average".to_string(),
                    rust_module_names: vec!["module".to_string()],
                    additional_client_flags: vec![],
                },
                Example {
                    name: "translator".to_string(),
                    rust_module_names: vec!["module".to_string()],
                    additional_client_flags: vec![],
                },
            ]
            .iter()
            .map(|example| run_example(example))
            .collect(),
        },
        "cpp" => unimplemented!("C++ examples not implemented yet"),
        v => panic!("unknown variant: {}", v),
    }
}

fn build_wasm_module(manifest_path: &str) -> Step {
    Step::Single {
        name: manifest_path.to_string(),
        command: Cmd::new(
            "cargo",
            &[
                "build",
                "--release",
                "--target=wasm32-unknown-unknown",
                &format!("--manifest-path={}", manifest_path),
            ],
        ),
    }
}

fn is_mac_os() -> bool {
    cfg!(macos)
}

fn bazel_build_flags() -> Vec<String> {
    let mut flags = vec![
        "--remote_cache=https://storage.googleapis.com/oak-bazel-cache".to_string(),
        "--block_for_lock=false".to_string(),
        "--show_timestamps".to_string(),
    ];

    const OAK_REMOTE_CACHE_KEY: &str = "./.oak_remote_cache_key.json";
    if Path::new(OAK_REMOTE_CACHE_KEY).exists() {
        flags.push(format!("--google_credentials={}", OAK_REMOTE_CACHE_KEY));
    } else {
        flags.push("--remote_upload_local_results=false".to_string());
    };

    flags
}

fn as_ref(v: &[String]) -> Vec<&str> {
    v.iter().map(|x| x.as_ref()).collect()
}

fn bazel_build(extra_build_flags: &[&str], targets: &[&str]) -> Cmd {
    let mut flags = Vec::new();
    flags.push("build");

    let b = bazel_build_flags();
    flags.extend(as_ref(&b));

    flags.extend(extra_build_flags);
    flags.push("--");
    flags.extend(targets);
    Cmd::new("bazel", &flags)
}

fn build_server(opt: &BuildServer) -> Step {
    match opt.variant.as_str() {
        "rust" => Step::Single {
            name: "build rust server".to_string(),
            command: Cmd::new(
                "cargo",
                &[
                    "build",
                    "--release",
                    "--target=x86_64-unknown-linux-musl",
                    "--package=oak_loader",
                ],
            ),
        },
        v => {
            let config = match v {
                "base" => {
                    if is_mac_os() {
                        "darwin"
                    } else {
                        "clang"
                    }
                }
                "logless" => "clang-logless",
                "arm" => "armv8",
                "asan" => "asan",
                "tsan" => "tsan",
                _ => panic!("unknown variant: {}", v),
            };
            Step::Single {
                name: "build cpp server".to_string(),
                command: bazel_build(
                    &[&format!("--config={}", config)],
                    &[
                        "//oak/server/loader:oak_runner",
                        "//oak/server/storage:storage_server",
                    ],
                ),
            }
        }
    }
}

fn run_tests() -> Step {
    Step::Multiple {
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
            perform_todo_check(),
        ],
    }
}

/// Returns all the files and directories under the examples directory.
fn examples() -> impl Iterator<Item = PathBuf> {
    let walker = walkdir::WalkDir::new("./examples").into_iter();
    walker
        .filter_entry(|e| !is_ignored_entry(e))
        .filter_map(Result::ok)
        .map(|e| e.into_path())
}

fn build_example_config(example_name: &str) -> Step {
    Step::Single {
        name: "build_config".to_string(),
        command: Cmd::new(
            "bazel",
            &[
                "build",
                &format!("//examples/{}/config:config", example_name),
            ],
        ),
    }
}

fn run_example_server(application_file: &str) -> Cmd {
    Cmd::new(
        "cargo",
        &[
            "run",
            "--release",
            "--target=x86_64-unknown-linux-musl",
            "--package=oak_loader",
            "--",
            "--grpc-tls-private-key=./examples/certs/local/local.key",
            "--grpc-tls-certificate=./examples/certs/local/local.pem",
            "--root-tls-certificate=./examples/certs/local/ca.pem",
            // TODO(#396): Add `--oidc-client` support.
            &format!("--application={}", application_file),
        ],
    )
}

struct Example {
    name: String,
    rust_module_names: Vec<String>,
    additional_client_flags: Vec<String>,
}

fn run_example(example: &Example) -> Step {
    Step::Multiple {
        name: example.name.to_string(),
        steps: vec![
            Step::Multiple {
                name: "build_wasm_modules".to_string(),
                steps: example
                    .rust_module_names
                    .iter()
                    .map(|rust_module_name| {
                        build_wasm_module(&format!(
                            "examples/{}/{}/rust/Cargo.toml",
                            example.name, rust_module_name
                        ))
                    })
                    .collect(),
            },
            build_example_config(&example.name),
            Step::WithBackground {
                name: "run_server".to_string(),
                background: run_example_server(&format!(
                    "./bazel-bin/examples/{}/config/config.bin",
                    example.name
                )),
                foreground: Box::new(Step::Single {
                    name: "run_client".to_string(),
                    command: Cmd::new(
                        "bazel",
                        vec![
                            "run".to_string(),
                            "--".to_string(),
                            format!("//examples/{}/client:client", example.name),
                            "--ca_cert=../../../../../../../../examples/certs/local/ca.pem"
                                .to_string(),
                        ]
                        .iter()
                        .chain(example.additional_client_flags.iter()),
                    ),
                }),
            },
        ],
    }
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

fn is_regular_file(path: &PathBuf) -> bool {
    path.is_file()
}

/// Return an iterator of all the first-party and non-ignored files in the repository, which can be
/// then additionally filtered by the caller.
fn source_files() -> impl Iterator<Item = PathBuf> {
    let walker = walkdir::WalkDir::new(".").into_iter();
    walker
        .filter_entry(|e| !is_ignored_entry(e))
        .filter_map(Result::ok)
        .map(|e| e.into_path())
        .filter(is_regular_file)
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

/// Return whether the provided path refers to a shell script file, by looking at the first
/// two bytes of the file.
fn is_shell_script(path: &PathBuf) -> bool {
    let mut file = std::fs::File::open(path).expect("could not open file");
    let mut prefix = [0u8; 2];
    let len = file.read(&mut prefix[..]).unwrap();
    len == 2 && prefix[0] == b'#' && prefix[1] == b'!'
}

fn run_buildifier() -> Step {
    Step::Multiple {
        name: "buildifier".to_string(),
        steps: source_files()
            .filter(is_bazel_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new("buildifier", &["-lint=warn", "-mode=check", &entry]),
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
                command: Cmd::new("prettier", &["--check", &entry]),
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
                command: Cmd::new("embedmd", &["-d", &entry]),
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
                command: Cmd::new(
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
                command: Cmd::new(
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
                command: Cmd::new(
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
                command: Cmd::new(
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
        command: Cmd::new("bazel", &["build", "--", "//oak/...:all"]),
    }
}

fn run_bazel_test() -> Step {
    Step::Single {
        name: "bazel test".to_string(),
        command: Cmd::new("bazel", &["test", "--", "//oak/...:all"]),
    }
}

fn perform_todo_check() -> Step {
    Step::Internal {
        name: format!("{}DO check", "TO"),
        execute: || {
            let statuses = source_files()
                .filter(|entry| !is_shell_script(entry))
                .map(|entry| TodoChecker::new(&entry).run());
            let status: SingleStatusResult = status_combine(statuses);
            status
        },
    }
}

pub fn to_string(path: PathBuf) -> String {
    path.to_str().unwrap().to_string()
}
