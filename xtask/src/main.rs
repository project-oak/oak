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
//! cargo run --manifest-path=xtask/Cargo.toml
//! ```

#![feature(async_closure)]

use clap::{IntoApp, Parser};
use colored::*;
use once_cell::sync::Lazy;
use std::{
    path::{Path, PathBuf},
    sync::Mutex,
};

#[macro_use]
mod internal;
use internal::*;

mod examples;
use examples::*;

mod files;
use files::*;

mod diffs;
use diffs::*;

mod check_todo;
use check_todo::CheckTodo;

mod check_license;
use check_license::CheckLicense;

mod check_build_licenses;
use check_build_licenses::CheckBuildLicenses;

mod launcher;

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

    let opt = Opt::parse();

    let run = async move || {
        let steps = match_cmd(&opt);
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

fn match_cmd(opt: &Opt) -> Step {
    match opt.cmd {
        Command::RunLauncherTest => launcher::run_launcher_test(),
        Command::RunOakFunctionsExamples(ref run_opt) => {
            run_oak_functions_examples(run_opt, &opt.scope)
        }
        Command::BuildOakFunctionsExample(ref opts) => {
            build_oak_functions_example(opts, &opt.scope)
        }
        Command::BuildOakFunctionsServerVariants(ref opt) => {
            build_oak_functions_server_variants(opt)
        }
        Command::RunTests => run_tests(),
        Command::RunCargoClippy => run_cargo_clippy(&opt.scope),
        Command::RunCargoTests(ref run_opt) => run_cargo_tests(run_opt, &opt.scope),
        Command::RunBazelTests => run_bazel_tests(),
        Command::RunCargoFuzz(ref opt) => run_cargo_fuzz(opt),
        Command::Format => format(&opt.scope),
        Command::CheckFormat => check_format(&opt.scope),
        Command::RunCi => run_ci(),
        Command::Completion(ref opt) => run_completion(opt),
        Command::RunCargoDeny => run_cargo_deny(),
        Command::RunCargoUdeps => run_cargo_udeps(&opt.scope),
        Command::RunCargoClean => run_cargo_clean(),
    }
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
        steps: vec![
            run_cargo_tests(&RunTestsOpt { cleanup: false }, &Scope::DiffToMain),
            run_bazel_tests(),
        ],
    }
}

fn run_cargo_tests(opt: &RunTestsOpt, scope: &Scope) -> Step {
    let all_affected_crates = all_affected_crates(scope);
    Step::Multiple {
        name: "cargo tests".to_string(),
        steps: vec![
            run_cargo_test(opt, &all_affected_crates),
            run_cargo_doc(&all_affected_crates),
        ],
    }
}

fn run_bazel_tests() -> Step {
    Step::Multiple {
        name: "bazel tests".to_string(),
        steps: vec![run_bazel_build(), run_bazel_test()],
    }
}

pub fn run_cargo_fuzz(opt: &RunCargoFuzz) -> Step {
    let cargo_manifests: Vec<PathBuf> = crate_manifest_files()
        .filter(|path| is_fuzzing_toml_file(path))
        .filter(|path| match &opt.crate_name {
            Some(crate_name) => {
                let mut crate_path = path.clone();
                crate_path.pop();
                crate_path.pop();
                crate_path.file_name().and_then(|s| s.to_str()).unwrap() == crate_name.as_str()
            }
            None => true,
        })
        .collect();

    Step::Multiple {
        name: "fuzzing".to_string(),
        steps: cargo_manifests
            .iter()
            .map(|path| run_fuzz_targets_in_crate(path, opt))
            .collect(),
    }
}

pub fn run_fuzz_targets_in_crate(path: &Path, opt: &RunCargoFuzz) -> Step {
    // `cargo-fuzz` can only run in the crate that contains the `fuzz` crate. So we need to use
    // `Cmd::new_in_dir` to execute the command inside the crate's directory. Pop the two components
    // (i.e., `fuzz/Cargo.toml`) to get to the crate path.
    let mut crate_path = path.to_path_buf();
    crate_path.pop();
    crate_path.pop();

    let cargo_manifest: CargoManifest = toml::from_str(&read_file(path))
        .unwrap_or_else(|err| panic!("could not parse cargo manifest file {:?}: {}", path, err));

    Step::Multiple {
        name: format!("fuzzing {:?}", &crate_path.file_name().unwrap()),
        steps: cargo_manifest
            .bin
            .iter()
            .filter(|binary| match &opt.target_name {
                Some(target_name) => &binary.name == target_name,
                None => true,
            })
            .map(|binary| Step::Single {
                name: binary.name.clone(),
                command: Cmd::new_in_dir(
                    "cargo-fuzz",
                    spread!["run".to_string(),
                        binary.name.clone(),
                        "--target=x86_64-unknown-linux-gnu".to_string(),
                        "--release".to_string(),
                        "--".to_string(),
                        ...opt.args
                    ],
                    &crate_path,
                ),
            })
            .collect(),
    }
}

fn format(scope: &Scope) -> Step {
    let modified_files = modified_files(scope);
    let modified_crates = directly_modified_crates(&modified_files);
    Step::Multiple {
        name: "format".to_string(),
        steps: vec![
            run_clang_format(FormatMode::Fix),
            run_buildifier(FormatMode::Fix),
            run_prettier(FormatMode::Fix),
            run_markdownlint(FormatMode::Fix),
            run_embedmd(FormatMode::Fix),
            run_cargo_fmt(FormatMode::Fix, &modified_crates),
        ],
    }
}

fn check_format(scope: &Scope) -> Step {
    let modified_files = modified_files(scope);
    let modified_crates = directly_modified_crates(&modified_files);

    Step::Multiple {
        name: "format".to_string(),
        steps: vec![
            run_check_license(&modified_files),
            run_check_build_licenses(&modified_files),
            run_check_todo(&modified_files),
            run_clang_format(FormatMode::Check),
            run_buildifier(FormatMode::Check),
            run_prettier(FormatMode::Check),
            run_markdownlint(FormatMode::Check),
            run_embedmd(FormatMode::Check),
            // TODO(#1304): Uncomment, when re-run from GitHub is fixed.
            // run_liche(),
            run_cargo_fmt(FormatMode::Check, &modified_crates),
            run_hadolint(),
            run_shellcheck(),
        ],
    }
}

fn run_completion(completion: &Completion) -> Step {
    let mut file = std::fs::File::create(completion.file_name.clone()).expect("file not created");
    clap_complete::generate(
        clap_complete::Shell::Bash,
        &mut Opt::command(),
        "xtask",
        &mut file,
    );

    // Return an empty step. Otherwise we cannot call run_completion from match_cmd.
    Step::Multiple {
        name: "cargo completion".to_string(),
        steps: vec![],
    }
}

fn run_ci() -> Step {
    // parse cmds for ./scripts/xtask from ci.yaml to keep them in sync
    let path_to_ci_yaml = ".github/workflows/ci.yaml";
    let file = std::fs::File::open(path_to_ci_yaml).expect("could not open file");
    let contents: serde_yaml::Value =
        serde_yaml::from_reader(file).expect("could not read file contents");
    let mut ci_cmds = contents["jobs"]["xtask"]["strategy"]["matrix"]["cmd"]
        .as_sequence()
        .unwrap()
        .iter()
        .map(|c| c.as_str().unwrap().split_whitespace().collect())
        .collect::<Vec<Vec<&str>>>();

    Step::Multiple {
        name: "ci".to_string(),
        steps: ci_cmds
            .iter_mut()
            .map(|cmd| {
                let mut call = vec!["xtask"];
                call.append(cmd);
                let opt = Opt::parse_from(call);
                match_cmd(&opt)
            })
            .collect(),
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
            .filter(|p| is_bazel_file(p))
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
            .filter(|p| is_markdown_file(p))
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
            .filter(|p| is_markdown_file(p))
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
            .filter(|p| is_markdown_file(p))
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
            .filter(|p| is_dockerfile(p))
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
            .filter(|p| is_shell_script(p))
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
                "python3",
                &[
                    "./third_party/run-clang-format/run-clang-format.py",
                    "--recursive",
                    "--exclude",
                    "*/node_modules",
                    // TODO(#2654): Remove once all crates are part of the same workspace again
                    "--exclude",
                    "*/target",
                    "--exclude",
                    "third_party",
                    "oak_functions",
                ],
            ),
        },
        FormatMode::Fix => Step::Multiple {
            name: "clang format".to_string(),
            steps: source_files()
                .filter(|p| is_clang_format_file(p))
                .map(to_string)
                .map(|entry| Step::Single {
                    name: entry.clone(),
                    command: Cmd::new("clang-format", &["-i", "-style=file", &entry]),
                })
                .collect(),
        },
    }
}

fn run_check_license(modified_files: &ModifiedContent) -> Step {
    Step::Multiple {
        name: "check license".to_string(),
        steps: source_files()
            .filter(|p| is_source_code_file(p))
            .map(to_string)
            .filter(|file| modified_files.contains(file))
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: CheckLicense::new(entry),
            })
            .collect(),
    }
}

fn run_check_build_licenses(modified_files: &ModifiedContent) -> Step {
    Step::Multiple {
        name: "check BUILD licenses".to_string(),
        steps: source_files()
            .filter(|p| is_build_file(p))
            .map(to_string)
            .filter(|file| modified_files.contains(file))
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: CheckBuildLicenses::new(entry),
            })
            .collect(),
    }
}

fn run_check_todo(modified_files: &ModifiedContent) -> Step {
    Step::Multiple {
        name: "check todo".to_string(),
        steps: source_files()
            .filter(|p| is_source_code_file(p))
            .map(to_string)
            .filter(|file| modified_files.contains(file))
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: CheckTodo::new(entry),
            })
            .collect(),
    }
}

fn run_cargo_fmt(mode: FormatMode, modified_crates: &ModifiedContent) -> Step {
    Step::Multiple {
        name: "cargo fmt".to_string(),
        steps: crate_manifest_files()
            .map(to_string)
            .filter(|path| modified_crates.contains(path))
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new(
                    "cargo",
                    spread![
                        "fmt",
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

fn run_cargo_test(opt: &RunTestsOpt, all_affected_crates: &ModifiedContent) -> Step {
    Step::Multiple {
        name: "cargo test".to_string(),
        steps: crate_manifest_files()
            // Exclude `fuzz` crates, as there are no tests and binaries should not be executed.
            .filter(|path| !is_fuzzing_toml_file(path))
            .filter(|path| all_affected_crates.contains_path(path))
            .map(|entry| {
                // Run `cargo test` in the directory of the crate, not the top-level directory.
                // This is needed as otherwise any crate-specific `.cargo/config.toml` files would
                // be ignored. If a crate does not have a config file, Cargo will just backtrack
                // up the tree and pick up the `.cargo/config.toml` file from the root directory.
                let test_run_step = |name| Step::Single {
                    name,
                    command: Cmd::new_in_dir(
                        "cargo",
                        &[
                            "test",
                            "--all-features",
                            &format!(
                                "--manifest-path={}",
                                entry.file_name().unwrap().to_str().unwrap()
                            ),
                        ],
                        entry.parent().unwrap(),
                    ),
                };

                // If `cleanup` is enabled, add a cleanup step to remove the generated files.
                if opt.cleanup {
                    Step::Multiple {
                        name: entry.to_str().unwrap().to_string(),
                        steps: vec![
                            test_run_step("run".to_string()),
                            Step::Single {
                                name: "cleanup".to_string(),
                                command: Cmd::new(
                                    "rm",
                                    &["-rf", entry.with_file_name("target").to_str().unwrap()],
                                ),
                            },
                        ],
                    }
                } else {
                    test_run_step(entry.to_str().unwrap().to_string())
                }
            })
            .collect(),
    }
}

fn run_cargo_doc(all_affected_crates: &ModifiedContent) -> Step {
    Step::Multiple {
        name: "cargo doc".to_string(),
        steps: crate_manifest_files()
            .map(to_string)
            .filter(|path| all_affected_crates.contains(path))
            .map(|entry| {
                let mut path = PathBuf::from(entry);
                path.pop();
                let path = to_string(path).replace("./", "");
                Step::Single {
                    name: path.clone(),
                    command: Cmd::new("bash", &["./scripts/check_docs", &path]),
                }
            })
            .collect(),
    }
}

fn run_cargo_clippy(scope: &Scope) -> Step {
    let all_affected_crates = all_affected_crates(scope);
    Step::Multiple {
        name: "cargo clippy".to_string(),
        steps: crate_manifest_files()
            .filter(|path| all_affected_crates.contains_path(path))
            .map(|entry| Step::Single {
                name: entry.to_str().unwrap().to_string(),
                command: Cmd::new_in_dir(
                    "cargo",
                    &[
                        "clippy",
                        "--all-targets",
                        "--all-features",
                        &format!(
                            "--manifest-path={}",
                            entry.file_name().unwrap().to_str().unwrap()
                        ),
                        "--no-deps",
                        "--",
                        "--deny=warnings",
                    ],
                    entry.parent().unwrap(),
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

fn run_cargo_udeps(scope: &Scope) -> Step {
    let all_affected_crates = all_affected_crates(scope);

    Step::Multiple {
        name: "cargo udeps".to_string(),
        steps: workspace_manifest_files()
            .map(to_string)
            .filter(|path| all_affected_crates.contains(path))
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new(
                    "cargo",
                    &[
                        "udeps",
                        &format!("--manifest-path={}", &entry),
                        "--all-targets",
                        // The depinfo backend seems much faster and precise.
                        "--backend=depinfo",
                        "--workspace",
                    ],
                ),
            })
            .collect(),
    }
}

fn run_cargo_clean() -> Step {
    Step::Multiple {
        name: "cargo clean".to_string(),
        steps: crate_manifest_files()
            .map(to_string)
            .map(|manifest_path| Step::Single {
                name: manifest_path.clone(),
                command: Cmd::new(
                    "cargo",
                    &["clean", &format!("--manifest-path={}", manifest_path)],
                ),
            })
            .collect(),
    }
}

fn run_bazel_build() -> Step {
    Step::Single {
        name: "bazel build".to_string(),
        command: Cmd::new(
            "bazel",
            &[
                "build",
                "--",
                "//oak_functions/client/java/...:all",
                "//oak_functions/examples/...:all",
                "//remote_attestation/java/...:all",
                "//java/...:all",
            ],
        ),
    }
}

fn run_bazel_test() -> Step {
    Step::Single {
        name: "bazel test".to_string(),
        command: Cmd::new(
            "bazel",
            &[
                "test",
                "--",
                "//oak_functions/client/java/...:all",
                "//oak_functions/examples/...:all",
                "//remote_attestation/java/tests/...:all",
                "//java/...:all",
            ],
        ),
    }
}
