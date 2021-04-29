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
use std::sync::Mutex;
use structopt::StructOpt;

#[macro_use]
mod internal;
use internal::*;

mod examples;
use examples::*;

mod files;
use files::*;

mod check_todo;
use check_todo::CheckTodo;

mod check_license;
use check_license::CheckLicense;

mod check_build_licenses;
use check_build_licenses::CheckBuildLicenses;

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
            Command::RunBench(ref opt) => run_benchmarks(opt.cleanup),
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

fn run_benchmarks(cleanup: bool) -> Step {
    Step::Multiple {
        name: "cargo bench".to_string(),
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
