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
use once_cell::sync::Lazy;
use std::{collections::HashMap, io::Read, path::PathBuf, sync::Mutex};
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
const ALL_CLIENTS: &str = "all";
const NO_CLIENTS: &str = "none";

/// Error message related to `Applications`
const INVALID_APP_COMBO_ERR: &str = "Invalid application combination: either classic or functions";

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

    let run = async move || {
        let steps = match opt.cmd {
            Command::RunExamples(ref opt) => run_examples(&opt),
            Command::RunFunctionsExamples(ref opt) => run_functions_examples(&opt),
            Command::BuildServer(ref opt) => build_server(&opt),
            Command::BuildFunctionsServer(ref opt) => build_functions_server(opt),
            Command::RunTests => run_tests(),
            Command::RunCargoTests(ref opt) => run_cargo_tests(opt.cleanup),
            Command::RunBazelTests => run_bazel_tests(),
            Command::RunTestsTsan => run_tests_tsan(),
            Command::Format => format(),
            Command::CheckFormat => check_format(),
            Command::RunCi => run_ci(),
            Command::Completion => panic!("should have been handled above"),
            Command::RunCargoDeny => run_cargo_deny(),
            Command::RunCargoUdeps => run_cargo_udeps(),
        };
        // TODO(#396): Add support for running individual commands via command line flags.
        let remaining_steps = steps.len();
        run_step(&Context::root(&opt), steps, Status::new(remaining_steps)).await
    };

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

    if !statuses.failed_steps_prefixes.is_empty() {
        eprintln!("List of failed steps:");
        statuses.failed_steps_prefixes.iter().for_each(|step| {
            eprintln!("{} ⊢ [{}]", step, StatusResultValue::Error);
        })
    }

    // If the overall status value is an error, terminate with a nonzero exit code.
    if statuses.values.contains(&StatusResultValue::Error) {
        std::process::exit(1);
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
        .filter(|example: &Example| example.applications.is_classic())
        .collect();
    Step::Multiple {
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
            .filter(|example| {
                example.applications.is_empty()
                    || example
                        .applications
                        .has_application(opt.application_variant.as_ref())
            })
            .map(|example| run_example(opt, example))
            .collect(),
    }
}

fn run_functions_examples(opt: &RunFunctionsExamples) -> Step {
    let examples: Vec<Example> = example_toml_files()
        .map(|path| {
            toml::from_str(&read_file(&path)).unwrap_or_else(|err| {
                panic!("could not parse example manifest file {:?}: {}", path, err)
            })
        })
        .filter(|example: &Example| !example.applications.is_classic())
        .collect();

    Step::Multiple {
        name: "oak-functions examples".to_string(),
        steps: examples
            .iter()
            .filter(|example| match &opt.example_name {
                Some(example_name) => &example.name == example_name,
                None => true,
            })
            .map(|example| run_functions_example(opt, example))
            .collect(),
    }
}

fn build_wasm_module(name: &str, target: &Target, example_name: &str) -> Step {
    match target {
        Target::Cargo {
            cargo_manifest,
            additional_build_args,
        } => {
            let metadata = cargo_metadata::MetadataCommand::new()
                .manifest_path(cargo_manifest)
                .exec()
                .unwrap();
            Step::Single {
                name: format!("wasm:{}:{}", name, cargo_manifest.to_string()),
                command: Cmd::new(
                    "cargo",
                    // Keep this in sync with `/oak_functions/sdk/test/utils/src/lib.rs`.
                    // Keep this in sync with `/sdk/rust/oak_tests/src/lib.rs`.
                    spread![
                        // `--out-dir` is unstable and requires `-Zunstable-options`.
                        "-Zunstable-options".to_string(),
                        "build".to_string(),
                        "--target=wasm32-unknown-unknown".to_string(),
                        // Use a fixed `--target-dir`, because it influences the SHA256 hash of the
                        // Wasm module.
                        //
                        // This directory is separate from `examples/target` because it is used by
                        // `cargo test`, which also executes [`oak_tests::compile_rust_wasm`] and
                        // thus runs `cargo build` inside it. It may lead to errors, since
                        // dependencies may be recompiled by `cargo build` and `cargo test` will
                        // fail to continue.
                        format!("--target-dir={}/wasm", metadata.target_directory),
                        format!("--manifest-path={}", cargo_manifest),
                        format!("--out-dir={}/bin", metadata.workspace_root),
                        "--release".to_string(),
                        ...additional_build_args
                    ],
                ),
            }
        }
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
    Step::Multiple {
        name: "server".to_string(),
        steps: vec![
            vec![Step::Single {
                name: "create bin folder".to_string(),
                command: Cmd::new(
                    "mkdir",
                    vec!["-p".to_string(), "oak_loader/bin".to_string()],
                ),
            }],
            match opt.server_variant {
                ServerVariant::Unsafe | ServerVariant::Coverage | ServerVariant::Experimental => vec![Step::Single {
                    name: "build introspection browser client".to_string(),
                    command: Cmd::new("npm",
                                      vec![
                                          "--prefix",
                                          "oak_runtime/introspection_browser_client",
                                          "run",
                                          "build",
                                      ])
                }],
                _ => vec![]
            },
            vec![
                build_rust_binary("oak_loader", opt,
                &if opt.server_variant == ServerVariant::Coverage {
                    hashmap! {
                        // Build the Runtime server in coverage mode, as per https://github.com/mozilla/grcov
                        "CARGO_INCREMENTAL".to_string() => "0".to_string(),
                        "RUSTDOCFLAGS".to_string() => "-Cpanic=abort".to_string(),
                        // grcov instructions suggest also including `-Cpanic=abort` in RUSTFLAGS, but this causes our build.rs scripts to fail.
                        "RUSTFLAGS".to_string() => "-Zprofile -Ccodegen-units=1 -Copt-level=0 -Clink-dead-code -Coverflow-checks=off -Zpanic-abort_tests".to_string(),
                    }
                } else {
                    hashmap! {}
                },)
            ],
        ].into_iter()
            .flatten()
            .collect::<Vec<_>>()
    }
}

fn build_functions_server(opt: &BuildFunctionsServer) -> Step {
    Step::Multiple {
        name: "server".to_string(),
        steps: vec![
            vec![Step::Single {
                name: "create bin folder".to_string(),
                command: Cmd::new(
                    "mkdir",
                    vec!["-p".to_string(), "oak_functions/loader/bin".to_string()],
                ),
            }],
            vec![build_rust_binary("oak_functions/loader", opt, &hashmap! {})],
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>(),
    }
}

fn build_rust_binary<T: RustBinaryOptions>(
    manifest_dir: &str,
    opt: &T,
    env: &HashMap<String, String>,
) -> Step {
    Step::Single {
        name: "build rust binary".to_string(),
        command: Cmd::new_with_env(
            "cargo",
            spread![
                ...match opt.server_rust_toolchain() {
                    // This overrides the toolchain used by `rustup` to invoke the actual
                    // `cargo` binary.
                    // See https://github.com/rust-lang/rustup#toolchain-override-shorthand
                    Some(server_rust_toolchain) => vec![format!("+{}", server_rust_toolchain)],
                    None => vec![],
                },
                "build".to_string(),
                format!("--manifest-path={}/Cargo.toml", manifest_dir),
                format!("--out-dir={}/bin", manifest_dir),
                // `--out-dir` is unstable and requires `-Zunstable-options`.
                "-Zunstable-options".to_string(),
                ...if !opt.features().is_empty() {
                    vec![format!("--features={}", opt.features())]
                } else {
                    vec![]
                },
                ...if opt.build_release() {
                    vec![format!("--target={}", opt.server_rust_target().as_deref().unwrap_or(DEFAULT_SERVER_RUST_TARGET)),
                    "--release".to_string() ]} else {vec![]},
            ],
            env,
        ),
    }
}

fn run_tests() -> Step {
    Step::Multiple {
        name: "tests".to_string(),
        steps: vec![run_cargo_tests(false), run_bazel_tests()],
    }
}

fn run_cargo_tests(cleanup: bool) -> Step {
    Step::Multiple {
        name: "cargo tests".to_string(),
        steps: vec![run_cargo_clippy(), run_cargo_test(cleanup), run_cargo_doc()],
    }
}

fn run_bazel_tests() -> Step {
    Step::Multiple {
        name: "bazel tests".to_string(),
        steps: vec![run_bazel_build(), run_bazel_test(), run_clang_tidy()],
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
            // TODO(#1304): Uncomment, when re-run from GitHub is fixed.
            // run_liche(),
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
            run_cargo_udeps(),
            build_server(&BuildServer {
                server_variant: ServerVariant::Base,
                server_rust_toolchain: None,
                server_rust_target: None,
            }),
            build_server(&BuildServer {
                server_variant: ServerVariant::NoIntrospectionClient,
                server_rust_toolchain: None,
                server_rust_target: None,
            }),
            build_server(&BuildServer {
                server_variant: ServerVariant::Unsafe,
                server_rust_toolchain: None,
                server_rust_target: None,
            }),
            build_server(&BuildServer {
                server_variant: ServerVariant::Coverage,
                server_rust_toolchain: None,
                server_rust_target: None,
            }),
            build_server(&BuildServer {
                server_variant: ServerVariant::Experimental,
                server_rust_toolchain: None,
                server_rust_target: None,
            }),
            run_tests(),
            run_tests_tsan(),
            run_examples(&RunExamples {
                application_variant: "rust".to_string(),
                permissions_file: "".to_string(),
                example_name: None,
                run_server: None,
                client_additional_args: Vec::new(),
                server_additional_args: Vec::new(),
                build_docker: false,
                build_client: BuildClient {
                    client_variant: ALL_CLIENTS.to_string(),
                    client_rust_toolchain: None,
                    client_rust_target: None,
                },
                build_server: BuildServer {
                    server_variant: ServerVariant::Experimental,
                    server_rust_toolchain: None,
                    server_rust_target: None,
                },
            }),
            run_examples(&RunExamples {
                application_variant: "cpp".to_string(),
                permissions_file: "".to_string(),
                example_name: None,
                run_server: None,
                client_additional_args: Vec::new(),
                server_additional_args: Vec::new(),
                build_docker: false,
                build_client: BuildClient {
                    client_variant: ALL_CLIENTS.to_string(),
                    client_rust_toolchain: None,
                    client_rust_target: None,
                },
                build_server: BuildServer {
                    server_variant: ServerVariant::Unsafe,
                    server_rust_toolchain: None,
                    server_rust_target: None,
                },
            }),
            // Package the Hello World application in a Docker image.
            run_examples(&RunExamples {
                application_variant: "rust".to_string(),
                permissions_file: "./examples/permissions/permissions.toml".to_string(),
                example_name: Some("hello_world".to_string()),
                run_server: Some(false),
                client_additional_args: Vec::new(),
                server_additional_args: Vec::new(),
                build_docker: true,
                build_client: BuildClient {
                    client_variant: NO_CLIENTS.to_string(),
                    client_rust_toolchain: None,
                    client_rust_target: None,
                },
                build_server: BuildServer {
                    server_variant: ServerVariant::Base,
                    server_rust_toolchain: None,
                    server_rust_target: None,
                },
            }),
            run_examples(&RunExamples {
                application_variant: "rust".to_string(),
                permissions_file: "".to_string(),
                example_name: Some("abitest".to_string()),
                run_server: Some(false),
                client_additional_args: Vec::new(),
                server_additional_args: Vec::new(),
                build_docker: true,
                build_client: BuildClient {
                    client_variant: NO_CLIENTS.to_string(),
                    client_rust_toolchain: None,
                    client_rust_target: None,
                },
                build_server: BuildServer {
                    server_variant: ServerVariant::Unsafe,
                    server_rust_toolchain: None,
                    server_rust_target: None,
                },
            }),
            run_functions_examples(&RunFunctionsExamples {
                application_variant: "rust".to_string(),
                example_name: None,
                run_server: None,
                client_additional_args: Vec::new(),
                server_additional_args: Vec::new(),
                build_docker: false,
                build_client: BuildClient {
                    client_variant: ALL_CLIENTS.to_string(),
                    client_rust_toolchain: None,
                    client_rust_target: None,
                },
                build_server: BuildFunctionsServer {
                    server_variant: FunctionsServerVariant::Unsafe,
                    server_rust_toolchain: None,
                    server_rust_target: None,
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
    permissions_file: &str,
) -> Box<dyn Runnable> {
    Cmd::new_with_env(
        "oak_loader/bin/oak_loader",
        spread![
            "--grpc-tls-certificate=./examples/certs/local/local.pem".to_string(),
            "--grpc-tls-private-key=./examples/certs/local/local.key".to_string(),
            "--http-tls-certificate=./examples/certs/local/local.pem".to_string(),
            "--http-tls-private-key=./examples/certs/local/local.key".to_string(),
            // TODO(#396): Add `--oidc-client` support.
            format!("--application={}", application_file),
            match opt.server_variant {
                ServerVariant::Base => format!("--permissions={}", permissions_file),
                // server variants that have `oak-unsafe` cannot accept a `permissions` file
                _ => "".to_string(),
            },
            ...match opt.server_variant {
                ServerVariant::Base => vec![],
                // server variants that have `oak-unsafe` need to specify `root-tls-certificate`
                _ => vec!["--root-tls-certificate=./examples/certs/local/ca.pem".to_string()],
            },
            ...example_server.additional_args.clone(),
            ...server_additional_args,
        ],
        &if opt.server_variant == ServerVariant::Coverage {
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

fn run_functions_example_server(
    example_server: &ExampleServer,
    application: &ApplicationFunctions,
) -> Box<dyn Runnable> {
    Cmd::new_with_env(
        "oak_functions/loader/bin/oak_functions_loader",
        spread![
            format!("--wasm-path={}", application.wasm_path),
            ...example_server.additional_args.clone(),
        ],
        &hashmap! {},
    )
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Example {
    name: String,
    #[serde(default)]
    server: ExampleServer,
    #[serde(default)]
    backends: HashMap<String, Executable>,
    applications: Applications,
    clients: HashMap<String, Executable>,
}

impl Example {
    fn construct_application_build_steps(&self, application_variant: &str) -> Vec<Step> {
        self.applications
            .construct_application_build_steps(application_variant, &self.name)
    }

    fn construct_example_server_run_step(
        &self,
        opt: either::Either<&RunExamples, &RunFunctionsExamples>,
        run_clients: Step,
    ) -> Step {
        self.applications
            .construct_example_server_run_step(opt, &self, run_clients)
    }

    fn construct_backend_build_steps(&self, build_client: &BuildClient) -> Vec<Step> {
        self.backends
            .iter()
            .map(move |(name, backend)| Step::Single {
                name: name.to_string(),
                command: build(&backend.target, build_client),
            })
            .collect()
    }

    /// Recursively constructs backend steps.
    fn construct_backend_run_steps(
        &self,
        run_server_clients: Step,
        build_client: &BuildClient,
    ) -> Step {
        self.backends
            .iter()
            // First iteration includes `run_server_clients` as a foreground step.
            .fold(run_server_clients, |backend_steps, (name, backend)| {
                Step::WithBackground {
                    name: name.to_string(),
                    // Each `backend` is included as background step.
                    background: run(&backend, &build_client, Vec::new()),
                    foreground: Box::new(backend_steps),
                }
            })
    }
}

/// A construct representing either an Oak Classic or an Oak Functions application.
///
/// The condition that only one of `classic` or `functions` should be non-empty is
/// checked in each operation of this struct. If neither or both are empty, the
/// operation panics with an error message.
#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Applications {
    classic: Option<HashMap<String, ApplicationClassic>>,
    functions: Option<HashMap<String, ApplicationFunctions>>,
}

impl Applications {
    fn is_classic(&self) -> bool {
        match (&self.classic, &self.functions) {
            (Some(_applications), None) => true,
            (None, Some(_applications)) => false,
            _ => panic!(INVALID_APP_COMBO_ERR),
        }
    }

    fn is_empty(&self) -> bool {
        match (&self.classic, &self.functions) {
            (Some(applications), None) => applications.is_empty(),
            (None, Some(applications)) => applications.is_empty(),
            _ => panic!(INVALID_APP_COMBO_ERR),
        }
    }

    fn has_application(&self, application_variant: &str) -> bool {
        match (&self.classic, &self.functions) {
            (Some(applications), None) => applications.get(application_variant).is_some(),
            (None, Some(applications)) => applications.get(application_variant).is_some(),
            _ => panic!(INVALID_APP_COMBO_ERR),
        }
    }

    fn construct_application_build_steps(
        &self,
        application_variant: &str,
        example_name: &str,
    ) -> Vec<Step> {
        match (&self.classic, &self.functions) {
            (Some(applications), None) => {
                if applications.is_empty() {
                    vec![]
                } else {
                    let application = applications.get(application_variant).unwrap_or_else(|| panic!(
                        "Unsupported application variant: {} (supported variants include: all, rust, cpp, go, nodejs, none)",
                        application_variant)
                    );
                    application.construct_application_build_steps(example_name)
                }
            }
            (None, Some(applications)) => {
                if applications.is_empty() {
                    vec![]
                } else {
                    let application = applications.get(application_variant).unwrap_or_else(|| panic!(
                        "Unsupported application variant: {} (supported variants include: all, rust, cpp, go, nodejs, none)",
                        application_variant)
                    );
                    application.construct_application_build_steps(example_name)
                }
            }
            _ => panic!(INVALID_APP_COMBO_ERR),
        }
    }

    fn construct_example_server_run_step(
        &self,
        opt: either::Either<&RunExamples, &RunFunctionsExamples>,
        example: &Example,
        run_clients: Step,
    ) -> Step {
        match (&self.classic, &self.functions) {
            (Some(applications), None) => {
                if applications.is_empty() {
                    run_clients
                } else {
                    let opt = opt
                        .left()
                        .expect("Oak Classic application run with RunExamples options.");

                    let application = applications.get(opt.application_variant.as_str()).unwrap_or_else(|| panic!(
                        "Unsupported application variant: {} (supported variants include: all, rust, cpp, go, nodejs, none)",
                        opt.application_variant.as_str())
                    );
                    application.construct_example_server_run_step(opt, example, run_clients)
                }
            }
            (None, Some(applications)) => {
                if applications.is_empty() {
                    run_clients
                } else {
                    let opt = opt
                        .right()
                        .expect("Oak Function application run with RunFunctionsExamples options.");

                    let application = applications.get(opt.application_variant.as_str()).unwrap_or_else(|| panic!(
                        "Unsupported application variant: {} (supported variants include: all, rust, cpp, go, nodejs, none)",
                        opt.application_variant.as_str())
                    );
                    application.construct_example_server_run_step(opt, example, run_clients)
                }
            }
            _ => panic!(INVALID_APP_COMBO_ERR),
        }
    }
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct ApplicationClassic {
    manifest: String,
    out: String,
    modules: HashMap<String, Target>,
}

impl ApplicationClassic {
    fn construct_application_build_steps(&self, example_name: &str) -> Vec<Step> {
        vec![
            Step::Multiple {
                name: "build wasm modules".to_string(),
                steps: self
                    .modules
                    .iter()
                    .map(|(name, target)| build_wasm_module(name, target, example_name))
                    .collect(),
            },
            Step::Single {
                name: "build application".to_string(),
                command: build_application(&self),
            },
        ]
    }

    fn construct_example_server_run_step(
        &self,
        opt: &RunExamples,
        example: &Example,
        run_clients: Step,
    ) -> Step {
        let run_server = run_example_server(
            &opt.build_server,
            &example.server,
            opt.server_additional_args.clone(),
            &self.out,
            &opt.permissions_file,
        );

        if opt.build_client.client_variant == NO_CLIENTS {
            Step::Single {
                name: "run server".to_string(),
                command: run_server,
            }
        } else {
            Step::WithBackground {
                name: "background server".to_string(),
                background: run_server,
                foreground: Box::new(run_clients),
            }
        }
    }
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct ApplicationFunctions {
    wasm_path: String,
    target: Target,
}

impl ApplicationFunctions {
    fn construct_application_build_steps(&self, example_name: &str) -> Vec<Step> {
        vec![build_wasm_module(example_name, &self.target, example_name)]
    }

    fn construct_example_server_run_step(
        &self,
        opt: &RunFunctionsExamples,
        example: &Example,
        run_clients: Step,
    ) -> Step {
        let run_server = run_functions_example_server(&example.server, &self);

        if opt.build_client.client_variant == NO_CLIENTS {
            Step::Single {
                name: "run server".to_string(),
                command: run_server,
            }
        } else {
            Step::WithBackground {
                name: "background server".to_string(),
                background: run_server,
                foreground: Box::new(run_clients),
            }
        }
    }
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
        #[serde(default)]
        additional_build_args: Vec<String>,
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

fn run_clients(
    example: &Example,
    build_client: &BuildClient,
    client_additional_args: Vec<String>,
) -> Step {
    Step::Multiple {
        name: "run clients".to_string(),
        steps: example
            .clients
            .iter()
            .filter(|(name, _)| match build_client.client_variant.as_str() {
                ALL_CLIENTS => true,
                client => *name == client,
            })
            .map(|(name, client)| {
                run_client(name, &client, &build_client, client_additional_args.clone())
            })
            .collect(),
    }
}

fn run_example(opt: &RunExamples, example: &Example) -> Step {
    let run_clients = run_clients(
        example,
        &opt.build_client,
        opt.client_additional_args.clone(),
    );

    // Build the run steps (if any) according to the provided flags.
    //
    // If `run-server` is enabled, then run the server as well as a potential backend, both in the
    // background.
    //
    // If `client-variant` is not 'none', then run the server and backend in the background, and the
    // clients in the foreground.
    #[allow(clippy::collapsible_if)]
    let run_backend_server_clients: Step = if opt.run_server.unwrap_or(true) {
        let run_server_clients =
            example.construct_example_server_run_step(either::Left(opt), run_clients);
        example.construct_backend_run_steps(run_server_clients, &opt.build_client)
    } else {
        run_clients
    };

    Step::Multiple {
        name: example.name.to_string(),
        steps: vec![
            example.construct_application_build_steps(opt.application_variant.as_ref()),
            if opt.run_server.unwrap_or(true) {
                // Build the server first so that when running it in the next step it will start up
                // faster.
                vec![build_server(&opt.build_server)]
            } else {
                vec![]
            },
            if opt.build_docker {
                vec![build_docker(&example)]
            } else {
                vec![]
            },
            example.construct_backend_build_steps(&opt.build_client),
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

fn run_functions_example(opt: &RunFunctionsExamples, example: &Example) -> Step {
    // build any backend server
    let run_clients = run_clients(
        example,
        &opt.build_client,
        opt.client_additional_args.clone(),
    );

    #[allow(clippy::collapsible_if)]
    let run_backend_server_clients: Step = if opt.run_server.unwrap_or(true) {
        let run_server_clients =
            example.construct_example_server_run_step(either::Right(opt), run_clients);
        example.construct_backend_run_steps(run_server_clients, &opt.build_client)
    } else {
        run_clients
    };

    Step::Multiple {
        name: example.name.to_string(),
        steps: vec![
            example.construct_application_build_steps(opt.application_variant.as_ref()),
            if opt.run_server.unwrap_or(true) {
                // Build the server first so that when running it in the next step it will start up
                // faster.
                vec![build_functions_server(&opt.build_server)]
            } else {
                vec![]
            },
            if opt.build_docker {
                vec![build_docker(&example)]
            } else {
                vec![]
            },
            example.construct_backend_build_steps(&opt.build_client),
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

fn build_application(application: &ApplicationClassic) -> Box<dyn Runnable> {
    Cmd::new(
        "cargo",
        vec![
            "run".to_string(),
            "--manifest-path=sdk/rust/oak_app_build/Cargo.toml".to_string(),
            "--".to_string(),
            format!("--manifest-path={}", application.manifest),
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
                        "--file=./oak_loader/Dockerfile",
                        "./oak_loader",
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
                        // An example may have more than one application, and the applications may
                        // have arbitrary names, so this is an approximation of the expected
                        // application file name of one of them.
                        &format!("--build-arg=application_file_name={}.oak", example.name),
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

fn build(target: &Target, opt: &BuildClient) -> Box<dyn Runnable> {
    match target {
        Target::Cargo {
            cargo_manifest,
            additional_build_args,
        } => Cmd::new(
            "cargo",
            spread![
                "build".to_string(),
                "--release".to_string(),
                format!(
                    "--target={}",
                    opt.client_rust_target
                        .as_deref()
                        .unwrap_or(DEFAULT_EXAMPLE_BACKEND_RUST_TARGET)
                ),
                format!("--manifest-path={}", cargo_manifest),
                ...additional_build_args,
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

fn run(
    executable: &Executable,
    opt: &BuildClient,
    additional_args: Vec<String>,
) -> Box<dyn Runnable> {
    match &executable.target {
        Target::Cargo {
            cargo_manifest,
            additional_build_args,
        } => Cmd::new(
            "cargo",
            spread![
                "run".to_string(),
                "--release".to_string(),
                format!("--target={}", opt.client_rust_target.as_deref().unwrap_or(DEFAULT_EXAMPLE_BACKEND_RUST_TARGET)),
                format!("--manifest-path={}", cargo_manifest),
                ...additional_build_args,
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
                "--ca_cert_path=../../../../../../../../../examples/certs/local/ca.pem".to_string(),
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

fn run_client(
    name: &str,
    executable: &Executable,
    opt: &BuildClient,
    additional_args: Vec<String>,
) -> Step {
    Step::Multiple {
        name: name.to_string(),
        steps: vec![
            Step::Single {
                name: "build".to_string(),
                command: build(&executable.target, &opt),
            },
            Step::Single {
                name: "run".to_string(),
                command: run(executable, &opt, additional_args),
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
        || components.contains(&std::path::Component::Normal("protoc_out".as_ref())) // Code generated by protoc
        || components.contains(&std::path::Component::Normal("dist".as_ref())) // Code generated by webpack
        || components.contains(&std::path::Component::Normal("target".as_ref())) // Rust artifacts.
        || components.contains(&std::path::Component::Normal("third_party".as_ref()))
}

fn is_ignored_entry(entry: &walkdir::DirEntry) -> bool {
    let path = entry.clone().into_path();
    // Simple heuristic to try and exclude generated files.
    is_ignored_path(&path) || file_contains(&path, "DO NOT EDIT")
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

/// Return an iterator of all known Cargo Manifest files that define crates.
fn crate_manifest_files() -> impl Iterator<Item = PathBuf> {
    source_files()
        .filter(is_cargo_toml_file)
        .filter(|p| is_cargo_package_file(p))
}

/// Return an iterator of all known Cargo Manifest files that define workspaces.
fn workspace_manifest_files() -> impl Iterator<Item = PathBuf> {
    source_files()
        .filter(is_cargo_toml_file)
        .filter(|p| is_cargo_workspace_file(p))
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
    filename.ends_with(".yaml") || filename.ends_with(".yml")
}

fn is_html_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".htm") || filename.ends_with(".html")
}

fn is_javascript_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".js") || filename.ends_with(".mjs")
}

fn is_typescript_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".ts") || filename.ends_with(".tsx")
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

fn file_contains(path: &PathBuf, pattern: &str) -> bool {
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
    // We run prettier as a single command on all the files at once instead of once per file,
    // because it takes a considerable time to start up for each invocation. See #1680.
    let files = source_files()
        .filter(|path| {
            is_markdown_file(path)
                || is_yaml_file(path)
                || is_toml_file(path)
                || is_html_file(path)
                || is_javascript_file(path)
                || is_typescript_file(path)
        })
        .map(to_string)
        .collect::<Vec<_>>();
    Step::Single {
        name: "prettier (coalesced)".to_string(),
        command: Cmd::new(
            "prettier",
            spread![
                match mode {
                    FormatMode::Check => "--check".to_string(),
                    FormatMode::Fix => "--write".to_string(),
                },
                ...files
            ],
        ),
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

// TODO(#1304): Re-enable dead-code check, when re-run from GitHub is fixed.
#[allow(dead_code)]
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
        steps: crate_manifest_files()
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new_with_env(
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
                    &hashmap! {
                        // rustfmt emits copious debug logs, leading to multi-minute
                        // runs if the user's env happens to have RUST_LOG=debug, so
                        // force a higher log level.
                        "RUST_LOG".to_string() => "warn".to_string(),
                    },
                ),
            })
            .collect(),
    }
}

fn run_cargo_test(cleanup: bool) -> Step {
    Step::Multiple {
        name: "cargo test".to_string(),
        steps: crate_manifest_files()
            .map(to_string)
            .map(|entry| {
                let test_run_step = |name| Step::Single {
                    name,
                    command: Cmd::new("cargo", &["test", &format!("--manifest-path={}", &entry)]),
                };
                let target_path = &entry.replace("Cargo.toml", "target");

                // If `cleanup` is enabled, add a cleanup step to remove the generated files. Do
                // this only if `target_path` is a non-empty, valid target path.
                if cleanup && !target_path.ends_with("/target") {
                    Step::Multiple {
                        name: entry.clone(),
                        steps: vec![
                            test_run_step("run".to_string()),
                            Step::Single {
                                name: "cleanup".to_string(),
                                command: Cmd::new("rm", &["-rf", target_path]),
                            },
                        ],
                    }
                } else {
                    test_run_step(entry.clone())
                }
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
        steps: crate_manifest_files()
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
                        // TODO(#1598): Re-enable lint when prost is fixed upstream.
                        "--allow=clippy::manual_strip",
                        // TODO(#1598): Re-enable lint when prost is fixed upstream.
                        "--allow=clippy::stable_sort_primitive",
                        // TODO(#1598): Re-enable lint when prost is fixed upstream.
                        "--allow=clippy::single-char-push-str",
                        // TODO(#1598): Re-enable lint when prost is fixed upstream.
                        "--allow=clippy::match-like-matches-macro",
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

fn run_cargo_udeps() -> Step {
    Step::Multiple {
        name: "cargo udeps".to_string(),
        steps: crate_manifest_files()
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new(
                    "cargo",
                    &[
                        "udeps",
                        &format!("--manifest-path={}", &entry),
                        "--all-targets",
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
