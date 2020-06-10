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

use colored::*;
use notify::Watcher;
use std::{
    collections::HashMap,
    io::Read,
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
};
use structopt::StructOpt;

mod internal;
use internal::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let opt = Opt::from_args();

    let watch = opt.watch;

    let run = move || {
        let steps = match opt.cmd {
            Command::RunExamples(ref opt) => run_examples(&opt),
            Command::BuildServer(ref opt) => build_server(&opt),
            Command::RunTests => run_tests(),
            Command::Format => format(),
            Command::RunCi => run_ci(),
        };
        // TODO(#396): Add support for running individual commands via command line flags.
        run_step(&Context::root(&opt), &steps)
    };

    if watch {
        let mut spinner: Option<spinners::Spinner>;

        fn new_spinner() -> spinners::Spinner {
            spinners::Spinner::new(
                spinners::Spinners::Pong,
                "waiting for events".purple().to_string(),
            )
        }

        let modified_files: Arc<Mutex<Vec<PathBuf>>> = Default::default();

        let modified_files_clone = modified_files.clone();
        let mut watcher: notify::RecommendedWatcher =
            notify::Watcher::new_immediate(move |res: notify::Result<notify::Event>| match res {
                Ok(event) => {
                    modified_files_clone.lock().unwrap().extend(
                        event
                            .paths
                            .iter()
                            .filter(|path| !is_ignored_path(path))
                            .cloned(),
                    );
                }
                Err(err) => panic!("watch error: {:?}", err),
            })?;
        watcher.watch(".", notify::RecursiveMode::Recursive)?;

        run();

        spinner = Some(new_spinner());
        loop {
            std::thread::sleep(std::time::Duration::from_millis(1_000));

            // Take the list of modified files out of the mutex and avoid holding the lock guard.
            let modified_files = std::mem::take(&mut *modified_files.lock().unwrap());

            if modified_files.is_empty() {
                continue;
            } else {
                if let Some(spinner) = spinner.take() {
                    spinner.stop()
                }
                eprintln!();
                eprintln!("{}", "event received; modified files:".purple());
                for path in modified_files.iter() {
                    eprintln!("{}", format!("- {:?}", path).purple());
                }
                eprintln!();
                run();
                eprintln!();
                spinner = Some(new_spinner());
            }
        }
    } else {
        let statuses = run();
        // If the overall status value is an error, terminate with a nonzero exit code.
        if statuses.contains(&StatusResultValue::Error) {
            std::process::exit(1);
        }
    }

    Ok(())
}

fn run_examples(opt: &RunExamples) -> Step {
    let examples: Vec<Example> = example_toml_files()
        .map(|path| {
            toml::from_str(&read_file(&path)).unwrap_or_else(|err| {
                panic!("could not parse example manifest file {:?}: {}", path, err)
            })
        })
        .collect();
    eprintln!("parsed examples manifest files: {:?}", examples);
    match opt.application_variant.as_str() {
        "rust" => Step::Multiple {
            name: "examples".to_string(),
            /// TODO(#396): Check that all the example folders are covered by an entry here, or
            /// explicitly ignored. This will probably require pulling out the `Vec<Example>` to a
            /// top-level method first.
            steps: examples
                .iter()
                .filter(|example| match &opt.example_name {
                    Some(example_name) => &example.name == example_name,
                    None => true,
                })
                .map(|example| run_example(opt, example))
                .collect(),
        },
        "cpp" => unimplemented!("C++ examples not implemented yet"),
        v => panic!("unknown variant: {}", v),
    }
}

fn build_wasm_module(name: &str, manifest_path: &str) -> Step {
    Step::Single {
        name: format!("wasm:{}:{}", name, manifest_path.to_string()),
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
        name: "tests".to_string(),
        steps: vec![
            run_buildifier(FormatMode::Check),
            run_prettier(FormatMode::Check),
            run_markdownlint(FormatMode::Check),
            run_liche(),
            run_cargo_fmt(FormatMode::Check),
            run_cargo_clippy(),
            run_cargo_test(),
            run_bazel_build(),
            run_bazel_test(),
        ],
    }
}

fn format() -> Step {
    Step::Multiple {
        name: "format".to_string(),
        steps: vec![
            run_buildifier(FormatMode::Fix),
            run_prettier(FormatMode::Fix),
            run_markdownlint(FormatMode::Fix),
            run_embedmd(FormatMode::Fix),
            run_cargo_fmt(FormatMode::Fix),
        ],
    }
}

fn run_ci() -> Step {
    Step::Multiple {
        name: "ci".to_string(),
        steps: vec![
            run_tests(),
            run_examples(&RunExamples {
                application_variant: "rust".to_string(),
                example_name: None,
                build_only: false,
            }),
        ],
    }
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

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Example {
    name: String,
    modules: HashMap<String, Target>,
    clients: HashMap<String, Client>,
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
enum Target {
    Bazel { bazel_target: String },
    Cargo { cargo_manifest: String },
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Client {
    #[serde(flatten)]
    target: Target,
    #[serde(default)]
    additional_args: Vec<String>,
}

fn run_example(opt: &RunExamples, example: &Example) -> Step {
    Step::Multiple {
        name: example.name.to_string(),
        steps: vec![
            vec![
                Step::Multiple {
                    name: "build_wasm_modules".to_string(),
                    steps: example
                        .modules
                        .iter()
                        .map(|(name, target)| match target {
                            Target::Cargo { cargo_manifest } => {
                                build_wasm_module(name, &cargo_manifest)
                            }
                            Target::Bazel { .. } => todo!(),
                        })
                        .collect(),
                },
                build_example_config(&example.name),
                // Build the server first so that when running it in the next step it will start up
                // faster.
                build_server(&BuildServer {
                    variant: "rust".to_string(),
                }),
            ],
            if opt.build_only {
                vec![]
            } else {
                vec![Step::WithBackground {
                    name: "run_server".to_string(),
                    background: run_example_server(&format!(
                        "./bazel-bin/examples/{}/config/config.bin",
                        example.name
                    )),
                    foreground: Box::new(Step::Multiple {
                        name: "run_client".to_string(),
                        steps: example
                            .clients
                            .iter()
                            .map(|(name, client)| run_client(name, &client))
                            .collect(),
                    }),
                }]
            },
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>(),
    }
}

fn run_client(name: &str, client: &Client) -> Step {
    match &client.target {
        Target::Cargo { .. } => todo!(),
        Target::Bazel { bazel_target } => Step::Single {
            name: format!("bazel:{}:{}", name, bazel_target),
            command: Cmd::new(
                "bazel",
                vec![
                    vec![
                        "run".to_string(),
                        "--".to_string(),
                        bazel_target.to_string(),
                        "--ca_cert=../../../../../../../../examples/certs/local/ca.pem".to_string(),
                    ],
                    client.additional_args.clone(),
                ]
                .iter()
                .flatten(),
            ),
        },
    }
}

/// Return whether to ignore the specified path. This is used by the `walker` package to efficiently
/// avoid descending into blacklisted directories.
fn is_ignored_path(path: &PathBuf) -> bool {
    let components = path.components().collect::<std::collections::HashSet<_>>();
    components.contains(&std::path::Component::Normal(".git".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-bin".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-cache".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-clang-oak".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-clang-out".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-client-oak".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-client-out".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-oak".as_ref()))
        || components.contains(&std::path::Component::Normal("bazel-out".as_ref()))
        || components.contains(&std::path::Component::Normal("cargo-cache".as_ref()))
        || components.contains(&std::path::Component::Normal("node_modules".as_ref()))
        || components.contains(&std::path::Component::Normal("target".as_ref())) // Rust artifacts.
        || components.contains(&std::path::Component::Normal("third_party".as_ref()))
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

fn example_toml_files() -> impl Iterator<Item = PathBuf> {
    source_files().filter(is_example_toml_file)
}

fn is_example_toml_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename == "example.toml"
}

fn read_file(path: &PathBuf) -> String {
    let mut file = std::fs::File::open(path).expect("could not open file");
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .expect("could not read file contents");
    contents
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

enum FormatMode {
    Check,
    Fix,
}

fn run_buildifier(mode: FormatMode) -> Step {
    Step::Multiple {
        name: "buildifier".to_string(),
        steps: source_files()
            .filter(is_bazel_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new(
                    "buildifier",
                    &[
                        "-lint=warn",
                        match mode {
                            FormatMode::Check => "-mode=check",
                            FormatMode::Fix => "-mode=fix",
                        },
                        &entry,
                    ],
                ),
            })
            .collect(),
    }
}

fn run_prettier(mode: FormatMode) -> Step {
    Step::Multiple {
        name: "prettier".to_string(),
        steps: source_files()
            .filter(is_markdown_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new(
                    "prettier",
                    &[
                        match mode {
                            FormatMode::Check => "--check",
                            FormatMode::Fix => "--write",
                        },
                        &entry,
                    ],
                ),
            })
            .collect(),
    }
}

fn run_markdownlint(mode: FormatMode) -> Step {
    Step::Multiple {
        name: "markdownlint".to_string(),
        steps: source_files()
            .filter(is_markdown_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new(
                    "markdownlint",
                    vec![
                        match mode {
                            FormatMode::Check => vec![],
                            FormatMode::Fix => vec!["--fix"],
                        },
                        vec![&entry],
                    ]
                    .iter()
                    .flatten(),
                ),
            })
            .collect(),
    }
}

fn run_embedmd(mode: FormatMode) -> Step {
    Step::Multiple {
        name: "embedmd".to_string(),
        steps: source_files()
            .filter(is_markdown_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new(
                    "embedmd",
                    &[
                        match mode {
                            FormatMode::Check => "-d",
                            FormatMode::Fix => "-w",
                        },
                        &entry,
                    ],
                ),
            })
            .collect(),
    }
}

fn run_liche() -> Step {
    Step::Multiple {
        name: "liche".to_string(),
        steps: source_files()
            .filter(is_markdown_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new("liche", &[
                    "--document-root=.",
                    // We exclude the following URLs from the checks:
                    // - https://groups.google.com/g/project-oak-discuss : not publicly accessible
                    // - https://crates.io/crates : returns 404 (see https://github.com/raviqqe/liche/issues/39)
                    "--exclude=(https://groups.google.com/g/project-oak-discuss|https://crates.io/crates)",
                    &entry,
                ]),
            })
            .collect(),
    }
}

fn run_cargo_fmt(mode: FormatMode) -> Step {
    Step::Multiple {
        name: "cargo fmt".to_string(),
        steps: workspace_manifest_files()
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new(
                    "cargo",
                    vec![
                        vec!["fmt", "--all", &format!("--manifest-path={}", &entry)],
                        match mode {
                            FormatMode::Check => vec!["--", "--check"],
                            FormatMode::Fix => vec![],
                        },
                    ]
                    .iter()
                    .flatten(),
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
                command: Cmd::new("cargo", &["test", &format!("--manifest-path={}", &entry)]),
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

pub fn to_string(path: PathBuf) -> String {
    path.to_str().unwrap().to_string()
}
