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
//! cargo run --manifest-path=runner/Cargo.toml
//! ```

#![feature(async_closure)]

use colored::*;
use maplit::hashmap;
use notify::Watcher;
use once_cell::sync::Lazy;
use std::{
    collections::HashMap,
    io::Read,
    path::PathBuf,
    sync::{Arc, Mutex},
};
use structopt::StructOpt;

#[macro_use]
mod internal;
use internal::*;

mod check_todo;
use check_todo::CheckTodo;

mod check_license;
use check_license::CheckLicense;

mod check_build_licenses;
use check_build_licenses::CheckBuildLicenses;

#[cfg(target_os = "macos")]
const DEFAULT_SERVER_RUST_TARGET: &str = "x86_64-apple-darwin";
#[cfg(not(target_os = "macos"))]
const DEFAULT_SERVER_RUST_TARGET: &str = "x86_64-unknown-linux-musl";

#[cfg(target_os = "macos")]
const DEFAULT_EXAMPLE_BACKEND_RUST_TARGET: &str = "x86_64-apple-darwin";
#[cfg(not(target_os = "macos"))]
const DEFAULT_EXAMPLE_BACKEND_RUST_TARGET: &str = "x86_64-unknown-linux-gnu";

static PROCESSES: Lazy<Mutex<Vec<i32>>> = Lazy::new(|| Mutex::new(Vec::new()));

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    std::panic::set_hook(Box::new(|panic_info| {
        let msg = match panic_info.payload().downcast_ref::<&'static str>() {
            Some(s) => *s,
            None => match panic_info.payload().downcast_ref::<String>() {
                Some(s) => &s[..],
                None => "Box<Any>",
            },
        };
        eprintln!();
        eprintln!();
        eprintln!("panic occurred: {}", msg.bright_white().on_red());
        cleanup();
    }));

    let opt = Opt::from_args();

    if let Command::Completion = opt.cmd {
        Opt::clap().gen_completions_to("runner", clap::Shell::Bash, &mut std::io::stdout());
        std::process::exit(0);
    };

    let watch = opt.watch;

    let run = async move || {
        let steps = match opt.cmd {
            Command::RunExamples(ref opt) => run_examples(&opt),
            Command::BuildServer(ref opt) => build_server(&opt),
            Command::RunTests => run_tests(),
            Command::RunTestsTsan => run_tests_tsan(),
            Command::Format => format(),
            Command::CheckFormat => check_format(),
            Command::RunCi => run_ci(),
            Command::Completion => panic!("should have been handled above"),
        };
        // TODO(#396): Add support for running individual commands via command line flags.
        run_step(&Context::root(&opt), steps).await
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

        run().await;

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
                // TODO(#396): This does not work well with async, the `run` function can only be
                // invoked once.
                // run().await;
                eprintln!();
                spinner = Some(new_spinner());
            }
        }
    } else {
        // This is a crude way of killing any potentially running process when receiving a Ctrl-C
        // signal. We collect all process IDs in the `PROCESSES` variable, regardless of whether
        // they have already been terminated, and we try to kill all of them when receiving the
        // signal.
        tokio::spawn(async {
            tokio::signal::ctrl_c()
                .await
                .expect("could not wait for signal");
            cleanup();
            std::process::exit(-1);
        });
        let statuses = run().await;
        // If the overall status value is an error, terminate with a nonzero exit code.
        if statuses.contains(&StatusResultValue::Error) {
            std::process::exit(1);
        }
    }

    Ok(())
}

fn cleanup() {
    eprintln!();
    eprintln!(
        "{}",
        "signal or panic received, killing outstanding processes"
            .bright_white()
            .on_red()
    );
    for pid in PROCESSES
        .lock()
        .expect("could not acquire processes lock")
        .iter()
    {
        // We intentionally don't print anything here as it may obscure more interesting
        // results from the current execution.
        internal::kill_process(*pid);
    }
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

fn build_wasm_module(name: &str, target: &Target, example_name: &str) -> Step {
    match target {
        Target::Cargo { cargo_manifest } => Step::Single {
            name: format!("wasm:{}:{}", name, cargo_manifest.to_string()),
            command: Cmd::new(
                "cargo",
                &[
                    // `--out-dir` is unstable and requires `-Zunstable-options`.
                    "-Zunstable-options",
                    "build",
                    "--release",
                    "--target=wasm32-unknown-unknown",
                    &format!("--manifest-path={}", cargo_manifest),
                    &format!("--out-dir=examples/{}/bin", example_name),
                ],
            ),
        },
        Target::Bazel {
            bazel_target,
            config,
        } => Step::Multiple {
            name: "wasm".to_string(),
            steps: vec![
                Step::Single {
                    name: format!("wasm:{}:{}", name, bazel_target.to_string()),
                    command: Cmd::new(
                        "bazel",
                        vec![
                            "build".to_string(),
                            format!("--config={}", config),
                            bazel_target.to_string(),
                        ],
                    ),
                },
                Step::Single {
                    name: "create bin folder".to_string(),
                    command: Cmd::new(
                        "mkdir",
                        vec!["-p".to_string(), format!("examples/{}/bin", example_name)],
                    ),
                },
                Step::Single {
                    name: "copy wasm module".to_string(),
                    command: Cmd::new(
                        "cp",
                        vec![
                            "-f".to_string(),
                            format!(
                                "bazel-{}-bin/{}",
                                match config.as_ref() {
                                    "emscripten" => "emscripten",
                                    "wasm32" => "wasm",
                                    _ => panic!("unsupported Bazel config: {}", config),
                                },
                                bazel_target.replace("//", "").replace(":", "/")
                            ),
                            format!("examples/{}/bin", example_name),
                        ],
                    ),
                },
            ],
        },
        Target::Npm { .. } => todo!(),
        Target::Shell { .. } => todo!(),
    }
}

fn build_server(opt: &BuildServer) -> Step {
    match opt.server_variant.as_str() {
        "base" | "logless" => Step::Multiple {
            name: "server".to_string(),
            steps: vec![
                Step::Single {
                    name: "create bin folder".to_string(),
                    command: Cmd::new(
                        "mkdir",
                        vec!["-p".to_string(), "oak/server/bin".to_string()],
                    ),
                },
                Step::Single {
                    name: format!("build server ({})", opt.server_variant),
                    command: Cmd::new_with_env(
                        "cargo",
                        spread![
                            ...match &opt.server_rust_toolchain {
                                // This overrides the toolchain used by `rustup` to invoke the actual
                                // `cargo` binary.
                                // See https://github.com/rust-lang/rustup#toolchain-override-shorthand
                                Some(server_rust_toolchain) => vec![format!("+{}", server_rust_toolchain)],
                                None => vec![],
                            },
                            "build".to_string(),
                            // If building in coverage mode, use the default target from the host, and build
                            // in debug mode.
                            ...if opt.coverage {
                                vec![]
                            } else {
                                vec![
                                    format!("--target={}", opt.server_rust_target.as_deref().unwrap_or(DEFAULT_SERVER_RUST_TARGET)),
                                    "--release".to_string(),
                                ]
                            },
                            "--manifest-path=oak/server/rust/oak_loader/Cargo.toml".to_string(),
                            "--out-dir=oak/server/bin".to_string(),
                            // `--out-dir` is unstable and requires `-Zunstable-options`.
                            "-Zunstable-options".to_string(),
                            ...if opt.server_variant == "logless" {
                                vec!["--no-default-features".to_string()]
                            } else {
                                vec![]
                            },
                        ],
                        &if opt.coverage {
                            hashmap! {
                                // Build the Runtime server in coverage mode, as per https://github.com/mozilla/grcov
                                "CARGO_INCREMENTAL".to_string() => "0".to_string(),
                                "RUSTDOCFLAGS".to_string() => "-Cpanic=abort".to_string(),
                                // grcov instructions suggest also including `-Cpanic=abort` in RUSTFLAGS, but this causes our build.rs scripts to fail.
                                "RUSTFLAGS".to_string() => "-Zprofile -Ccodegen-units=1 -Copt-level=0 -Clink-dead-code -Coverflow-checks=off -Zpanic-abort_tests".to_string(),
                            }
                        } else {
                            hashmap! {}
                        },
                    ),
                },
            ],
        },
        v => panic!("unknown server variant: {}", v),
    }
}

fn run_tests() -> Step {
    Step::Multiple {
        name: "tests".to_string(),
        steps: vec![
            run_cargo_clippy(),
            run_cargo_test(),
            run_cargo_doc(),
            run_bazel_build(),
            run_bazel_test(),
            run_clang_tidy(),
        ],
    }
}

fn run_tests_tsan() -> Step {
    Step::Multiple {
        name: "tests".to_string(),
        steps: vec![run_cargo_test_tsan()],
    }
}

fn format() -> Step {
    Step::Multiple {
        name: "format".to_string(),
        steps: vec![
            run_clang_format(FormatMode::Fix),
            run_buildifier(FormatMode::Fix),
            run_prettier(FormatMode::Fix),
            run_markdownlint(FormatMode::Fix),
            run_embedmd(FormatMode::Fix),
            run_cargo_fmt(FormatMode::Fix),
        ],
    }
}

fn check_format() -> Step {
    Step::Multiple {
        name: "format".to_string(),
        steps: vec![
            run_check_license(),
            run_check_build_licenses(),
            run_check_todo(),
            run_clang_format(FormatMode::Check),
            run_buildifier(FormatMode::Check),
            run_prettier(FormatMode::Check),
            run_markdownlint(FormatMode::Check),
            run_embedmd(FormatMode::Check),
            run_liche(),
            run_cargo_fmt(FormatMode::Check),
            run_hadolint(),
            run_shellcheck(),
        ],
    }
}

fn run_ci() -> Step {
    Step::Multiple {
        name: "ci".to_string(),
        steps: vec![
            check_format(),
            run_cargo_deny(),
            build_server(&BuildServer {
                server_variant: "base".to_string(),
                server_rust_toolchain: None,
                server_rust_target: None,
                coverage: false,
            }),
            build_server(&BuildServer {
                server_variant: "logless".to_string(),
                server_rust_toolchain: None,
                server_rust_target: None,
                coverage: false,
            }),
            run_tests(),
            run_tests_tsan(),
            run_examples(&RunExamples {
                application_variant: "rust".to_string(),
                example_name: None,
                run_server: None,
                run_clients: None,
                client_additional_args: Vec::new(),
                server_additional_args: Vec::new(),
                build_docker: false,
                build_server: BuildServer {
                    server_variant: "base".to_string(),
                    server_rust_toolchain: None,
                    server_rust_target: None,
                    coverage: false,
                },
            }),
            // Package the Hello World application in a Docker image.
            run_examples(&RunExamples {
                application_variant: "rust".to_string(),
                example_name: Some("hello_world".to_string()),
                run_server: Some(false),
                run_clients: Some(false),
                client_additional_args: Vec::new(),
                server_additional_args: Vec::new(),
                build_docker: true,
                build_server: BuildServer {
                    server_variant: "base".to_string(),
                    server_rust_toolchain: None,
                    server_rust_target: None,
                    coverage: false,
                },
            }),
        ],
    }
}

fn run_example_server(
    opt: &BuildServer,
    example_server: &ExampleServer,
    server_additional_args: Vec<String>,
    application_file: &str,
) -> Box<dyn Runnable> {
    Cmd::new_with_env(
        "oak/server/bin/oak_loader",
        spread![
            "--grpc-tls-private-key=./examples/certs/local/local.key".to_string(),
            "--grpc-tls-certificate=./examples/certs/local/local.pem".to_string(),
            // TODO(#396): Add `--oidc-client` support.
            format!("--application={}", application_file),
            ...if opt.server_variant == "logless" {
                vec!["--no-default-features".to_string()]
            } else {
                vec!["--root-tls-certificate=./examples/certs/local/ca.pem".to_string()]
            },
            ...example_server.additional_args.clone(),
            ...server_additional_args,
        ],
        &if opt.coverage {
            hashmap! {
                // Build the Runtime server in coverage mode, as per https://github.com/mozilla/grcov
                "CARGO_INCREMENTAL".to_string() => "0".to_string(),
                "RUSTDOCFLAGS".to_string() => "-Cpanic=abort".to_string(),
                // grcov instructions suggest also including `-Cpanic=abort` in RUSTFLAGS, but this causes our build.rs scripts to fail.
                "RUSTFLAGS".to_string() => "-Zprofile -Ccodegen-units=1 -Copt-level=0 -Clink-dead-code -Coverflow-checks=off -Zpanic-abort_tests".to_string(),
            }
        } else {
            hashmap! {}
        },
    )
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Example {
    name: String,
    #[serde(default)]
    server: ExampleServer,
    #[serde(default)]
    backend: Option<Executable>,
    application: Application,
    modules: HashMap<String, Target>,
    clients: HashMap<String, Executable>,
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Application {
    manifest: String,
    out: String,
}

#[derive(serde::Deserialize, Debug, Default)]
#[serde(deny_unknown_fields)]
struct ExampleServer {
    #[serde(default)]
    additional_args: Vec<String>,
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
enum Target {
    Bazel {
        bazel_target: String,
        #[serde(default)]
        config: String,
    },
    Cargo {
        cargo_manifest: String,
    },
    Npm {
        package_directory: String,
    },
    Shell {
        script: String,
    },
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Executable {
    #[serde(flatten)]
    target: Target,
    #[serde(default)]
    additional_args: Vec<String>,
}

fn run_example(opt: &RunExamples, example: &Example) -> Step {
    let run_server = run_example_server(
        &opt.build_server,
        &example.server,
        opt.server_additional_args.clone(),
        &example.application.out,
    );
    let run_clients = Step::Multiple {
        name: "run clients".to_string(),
        steps: example
            .clients
            .iter()
            .map(|(name, client)| run_client(name, &client, opt.client_additional_args.clone()))
            .collect(),
    };

    // Build the run steps (if any) according to the provided flags.
    //
    // If `run-server` is enabled, then run the server as well as a potential backend, both in the
    // background.
    //
    // If `run-clients` is enabled, then run the server and backend in the background, and the
    // clients in the foreground.
    #[allow(clippy::collapsible_if)]
    let run_backend_server_clients: Step = if opt.run_server.unwrap_or(true) {
        let run_server_clients = if opt.run_clients.unwrap_or(true) {
            Step::WithBackground {
                name: "background server".to_string(),
                background: run_server,
                foreground: Box::new(run_clients),
            }
        } else {
            Step::Single {
                name: "run server".to_string(),
                command: run_server,
            }
        };
        match &example.backend {
            Some(backend) => Step::WithBackground {
                name: "background backend".to_string(),
                background: run(&backend, Vec::new()),
                foreground: Box::new(run_server_clients),
            },
            None => run_server_clients,
        }
    } else {
        if opt.run_clients.unwrap_or(true) {
            run_clients
        } else {
            Step::Multiple {
                name: "run clients (empty)".to_string(),
                steps: vec![],
            }
        }
    };

    Step::Multiple {
        name: example.name.to_string(),
        steps: vec![
            vec![
                Step::Multiple {
                    name: "build wasm modules".to_string(),
                    steps: example
                        .modules
                        .iter()
                        .map(|(name, target)| build_wasm_module(name, target, &example.name))
                        .collect(),
                },
                Step::Single {
                    name: "build application".to_string(),
                    command: build_application(&example.application),
                },
                // Build the server first so that when running it in the next step it will start up
                // faster.
                build_server(&opt.build_server),
            ],
            if opt.build_docker {
                vec![build_docker(&example)]
            } else {
                vec![]
            },
            match &example.backend {
                Some(backend) => vec![Step::Single {
                    name: "build backend".to_string(),
                    command: build(&backend.target),
                }],
                None => vec![],
            },
            vec![Step::Multiple {
                name: "run".to_string(),
                steps: vec![run_backend_server_clients],
            }],
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>(),
    }
}

fn build_application(application: &Application) -> Box<dyn Runnable> {
    Cmd::new(
        "cargo",
        vec![
            "run".to_string(),
            "--manifest-path=sdk/rust/oak_config_serializer/Cargo.toml".to_string(),
            "--".to_string(),
            format!("--input-file={}", application.manifest),
            format!("--output-file={}", application.out),
        ],
    )
}

fn build_docker(example: &Example) -> Step {
    Step::Multiple {
        name: "docker".to_string(),
        steps: vec![
            Step::Single {
                name: "build server image".to_string(),
                command: Cmd::new(
                    "docker",
                    &[
                        "build",
                        "--tag=oak_docker",
                        "--file=./oak/server/Dockerfile",
                        "./oak/server",
                    ],
                ),
            },
            Step::Single {
                name: "build example image".to_string(),
                command: Cmd::new(
                    "docker",
                    &[
                        "build",
                        &format!("--tag={}", example.name),
                        "--file=./examples/Dockerfile",
                        &format!("./examples/{}", example.name),
                    ],
                ),
            },
            Step::Single {
                name: "save example image".to_string(),
                command: Cmd::new(
                    "docker",
                    &[
                        "save",
                        &example.name,
                        &format!(
                            "--output=./examples/{}/bin/{}.tar",
                            example.name, example.name
                        ),
                    ],
                ),
            },
        ],
    }
}

fn build(target: &Target) -> Box<dyn Runnable> {
    match target {
        Target::Cargo { cargo_manifest } => Cmd::new(
            "cargo",
            vec![
                "build".to_string(),
                "--release".to_string(),
                format!("--target={}", DEFAULT_EXAMPLE_BACKEND_RUST_TARGET),
                format!("--manifest-path={}", cargo_manifest),
            ],
        ),
        Target::Bazel {
            bazel_target,
            config,
        } => Cmd::new(
            "bazel",
            spread![
                "build".to_string(),
                ...if config.is_empty() {
                    vec![]
                } else {
                    vec![format!("--config={}", config)]
                },
                bazel_target.to_string(),
            ],
        ),
        Target::Npm { package_directory } => Cmd::new(
            "npm",
            vec!["ci".to_string(), format!("--prefix={}", package_directory)],
        ),
        Target::Shell { script } => Cmd::new("bash", &[script]),
    }
}

fn run(executable: &Executable, additional_args: Vec<String>) -> Box<dyn Runnable> {
    match &executable.target {
        Target::Cargo { cargo_manifest } => Cmd::new(
            "cargo",
            spread![
                "run".to_string(),
                "--release".to_string(),
                format!("--target={}", DEFAULT_EXAMPLE_BACKEND_RUST_TARGET),
                format!("--manifest-path={}", cargo_manifest),
                "--".to_string(),
                ...executable.additional_args.clone(),
                ...additional_args,
            ],
        ),
        Target::Bazel {
            bazel_target,
            config,
        } => Cmd::new(
            "bazel",
            spread![
                "run".to_string(),
                ...if config.is_empty() {
                    vec![]
                } else {
                    vec![format!("--config={}", config)]
                },
                "--".to_string(),
                bazel_target.to_string(),
                "--ca_cert=../../../../../../../../examples/certs/local/ca.pem".to_string(),
                ...executable.additional_args.clone(),
                ...additional_args,
            ],
        ),
        Target::Npm { package_directory } => Cmd::new(
            "npm",
            vec![
                "start".to_string(),
                format!("--prefix={}", package_directory),
            ],
        ),
        Target::Shell { script } => Cmd::new("bash", &[script]),
    }
}

fn run_client(name: &str, executable: &Executable, additional_args: Vec<String>) -> Step {
    Step::Multiple {
        name: name.to_string(),
        steps: vec![
            Step::Single {
                name: "build".to_string(),
                command: build(&executable.target),
            },
            Step::Single {
                name: "run".to_string(),
                command: run(executable, additional_args),
            },
        ],
    }
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

/// Return whether the provided path refers to a source file in a programming language.
fn is_source_code_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".cc")
        || filename.ends_with(".h")
        || filename.ends_with(".rs")
        || filename.ends_with(".proto")
        || filename.ends_with(".js")
        || filename.ends_with(".go")
}

/// Return whether the provided path refers to a source file that can be formatted by clang-tidy.
fn is_clang_format_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".cc") || filename.ends_with(".h") || filename.ends_with(".proto")
}

/// Return whether the provided path refers to a Bazel file (`BUILD`, `WORKSPACE`, or `*.bzl`)
fn is_bazel_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename == "BUILD" || filename == "WORKSPACE" || filename.ends_with(".bzl")
}

fn is_build_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename == "BUILD"
}

/// Return whether the provided path refers to a markdown file (`*.md`)
fn is_markdown_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".md")
}

fn is_dockerfile(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with("Dockerfile")
}

fn is_toml_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".toml")
}

fn is_yaml_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".yaml")
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

fn is_shell_script(path: &PathBuf) -> bool {
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
            .filter(|path| is_markdown_file(path) || is_yaml_file(path) || is_toml_file(path))
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
                    spread![
                        ...match mode {
                            FormatMode::Check => vec![],
                            FormatMode::Fix => vec!["--fix".to_string()],
                        },
                        entry,
                    ],
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
                    // - https://codecov.io/gh/project-oak/oak : unstable, and often unaccessible on CI-build
                    "--exclude=(https://groups.google.com/g/project-oak-discuss|https://crates.io/crates|https://codecov.io/gh/project-oak/oak)",
                    &entry,
                ]),
            })
            .collect(),
    }
}

fn run_hadolint() -> Step {
    Step::Multiple {
        name: "hadolint".to_string(),
        steps: source_files()
            .filter(is_dockerfile)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new("hadolint", &[entry]),
            })
            .collect(),
    }
}

fn run_shellcheck() -> Step {
    Step::Multiple {
        name: "shellcheck".to_string(),
        steps: source_files()
            .filter(is_shell_script)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new("shellcheck", &["--external-sources", &entry]),
            })
            .collect(),
    }
}

fn run_clang_format(mode: FormatMode) -> Step {
    match mode {
        FormatMode::Check => Step::Single {
            name: "clang format".to_string(),
            command: Cmd::new(
                "python",
                &[
                    "./third_party/run-clang-format/run-clang-format.py",
                    "-r",
                    "--exclude",
                    "*/node_modules",
                    "oak",
                    "examples",
                ],
            ),
        },
        FormatMode::Fix => Step::Multiple {
            name: "clang format".to_string(),
            steps: source_files()
                .filter(is_clang_format_file)
                .map(to_string)
                .map(|entry| Step::Single {
                    name: entry.clone(),
                    command: Cmd::new("clang-format", &["-i", "-style=file", &entry]),
                })
                .collect(),
        },
    }
}

fn run_check_license() -> Step {
    Step::Multiple {
        name: "check license".to_string(),
        steps: source_files()
            .filter(is_source_code_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: CheckLicense::new(entry),
            })
            .collect(),
    }
}

fn run_check_build_licenses() -> Step {
    Step::Multiple {
        name: "check BUILD licenses".to_string(),
        steps: source_files()
            .filter(is_build_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: CheckBuildLicenses::new(entry),
            })
            .collect(),
    }
}

fn run_check_todo() -> Step {
    Step::Multiple {
        name: "check todo".to_string(),
        steps: source_files()
            .filter(is_source_code_file)
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: CheckTodo::new(entry),
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
                    spread![
                        "fmt",
                        "--all",
                        format!("--manifest-path={}", &entry).as_ref(),
                        ...match mode {
                            FormatMode::Check => vec!["--", "--check"],
                            FormatMode::Fix => vec![],
                        },
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
                command: Cmd::new("cargo", &["test", &format!("--manifest-path={}", &entry)]),
            })
            .collect(),
    }
}

fn run_cargo_doc() -> Step {
    Step::Single {
        name: "cargo doc".to_string(),
        command: Cmd::new("bash", &["./scripts/check_docs"]),
    }
}

fn run_clang_tidy() -> Step {
    Step::Single {
        name: "clang tidy".to_string(),
        command: Cmd::new("bash", &["./scripts/run_clang_tidy"]),
    }
}

fn run_cargo_test_tsan() -> Step {
    Step::Single {
        name: "cargo test (tsan)".to_string(),
        command: Cmd::new_with_env(
            "cargo",
            &[
                "-Zbuild-std",
                "test",
                "--manifest-path=./examples/abitest/module_0/rust/Cargo.toml",
                "--target=x86_64-unknown-linux-gnu",
                "--verbose",
                "--",
                "--nocapture",
            ],
            &hashmap! {
                "RUST_BACKTRACE".to_string() => "1".to_string(),
                "RUSTFLAGS".to_string() => "-Z sanitizer=thread".to_string(),
                "TSAN_OPTIONS".to_string() => format!("halt_on_error=1 report_atomic_races=0 suppressions={}/.tsan_suppress", std::env::current_dir().unwrap().display()),
            },
        ),
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

fn run_cargo_deny() -> Step {
    Step::Multiple {
        name: "cargo deny".to_string(),
        steps: workspace_manifest_files()
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new(
                    "cargo",
                    &["deny", &format!("--manifest-path={}", &entry), "check"],
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
