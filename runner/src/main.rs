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
use std::{
    path::{Path, PathBuf},
    sync::Mutex,
};
use structopt::StructOpt;

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

    if let Command::Completion(completion) = opt.cmd {
        let mut out_dir = completion.out_dir;
        out_dir.push(".runner_bash_completion");
        let mut file = std::fs::File::create(out_dir)?;
        Opt::clap().gen_completions_to("runner", clap::Shell::Bash, &mut file);
        std::process::exit(0);
    };

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
        Command::RunExamples(ref opt) => run_examples(opt),
        Command::RunFunctionsExamples(ref opt) => run_functions_examples(opt),
        Command::BuildFunctionsExample(ref opt) => build_functions_example(opt),
        Command::BuildServer(ref opt) => build_server(opt, vec![]),
        Command::BuildFunctionsServer(ref opt) => build_functions_server(opt, vec![]),
        Command::RunTests => run_tests(),
        Command::RunCargoTests(ref opt) => run_cargo_tests(opt),
        Command::RunBazelTests => run_bazel_tests(),
        Command::RunTestsTsan => run_tests_tsan(),
        Command::RunCargoFuzz(ref opt) => run_cargo_fuzz(opt),
        Command::Format(ref commits) => format(commits),
        Command::CheckFormat(ref commits) => check_format(commits),
        Command::RunCi => run_ci(),
        Command::Completion(_) => panic!("should have been handled before"),
        Command::RunCargoDeny => run_cargo_deny(),
        Command::RunCargoUdeps => run_cargo_udeps(),
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
            run_cargo_tests(&RunTestsOpt {
                cleanup: false,
                commits: Commits::default(),
            }),
            run_bazel_tests(),
        ],
    }
}

fn run_cargo_tests(opt: &RunTestsOpt) -> Step {
    let all_affected_crates = all_affected_crates(&opt.commits);
    Step::Multiple {
        name: "cargo tests".to_string(),
        steps: vec![
            run_cargo_clippy(&all_affected_crates),
            run_cargo_test(opt, &all_affected_crates),
            run_cargo_doc(&all_affected_crates),
        ],
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

pub fn run_cargo_fuzz(opt: &RunCargoFuzz) -> Step {
    let steps = if opt.build_deps {
        vec![build_fuzz_dependencies(opt), run_fuzz_targets(opt)]
    } else {
        vec![run_fuzz_targets(opt)]
    };

    Step::Multiple {
        name: "cargo fuzz".to_string(),
        steps,
    }
}

pub fn build_fuzz_dependencies(opt: &RunCargoFuzz) -> Step {
    let fuzz_configs: Vec<FuzzConfig> = fuzz_config_toml_files()
        .filter(|path| match &opt.crate_name {
            Some(crate_name) => {
                let mut crate_path = path.clone();
                crate_path.pop();
                crate_path.pop();
                crate_path.file_name().and_then(|s| s.to_str()).unwrap() == crate_name.as_str()
            }
            None => true,
        })
        .map(|path| {
            toml::from_str(&read_file(&path)).unwrap_or_else(|err| {
                panic!("could not parse example manifest file {:?}: {}", path, err)
            })
        })
        .collect();

    Step::Multiple {
        name: "configure fuzzing".to_string(),
        steps: fuzz_configs.iter().map(run_fuzz_config).collect(),
    }
}

fn run_fuzz_config(config: &FuzzConfig) -> Step {
    Step::Multiple {
        name: "run".to_string(),
        steps: config
            .examples
            .iter()
            .map(|config| {
                let target = Target::Cargo {
                    cargo_manifest: config.manifest_path.clone(),
                    additional_build_args: vec![],
                };

                Step::Multiple {
                    name: config.name.clone(),
                    steps: vec![
                        // Build the .wasm file
                        build_wasm_module(&config.name, &target, &config.name),
                        // Additional step for copying `.wasm` file to the desired output dir
                        copy_wasm_file(config),
                    ],
                }
            })
            .collect(),
    }
}

fn copy_wasm_file(config: &FuzzableExample) -> Step {
    let metadata = cargo_metadata::MetadataCommand::new()
        .manifest_path(&config.manifest_path)
        .exec()
        .unwrap();
    let command = Cmd::new(
        "cp",
        vec![
            format!("{}/bin/{}.wasm", metadata.workspace_root, &config.name),
            format!("{}/{}.wasm", &config.out_dir, &config.name),
        ],
    );

    Step::Multiple {
        name: "copy to dir".to_string(),
        steps: vec![
            Step::Single {
                name: "mkdir".to_string(),
                command: Cmd::new("mkdir", vec!["--parents", &config.out_dir]),
            },
            Step::Single {
                name: "copy".to_string(),
                command,
            },
        ],
    }
}

pub fn run_fuzz_targets(opt: &RunCargoFuzz) -> Step {
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

fn format(commits: &Commits) -> Step {
    let modified_crates = directly_modified_crates(commits);
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

fn check_format(commits: &Commits) -> Step {
    let modified_files = modified_files(commits);
    let modified_crates = directly_modified_crates(commits);

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

fn run_ci() -> Step {
    // parse cmds for ./scripts/runner from ci.yaml to keep them in sync
    let path_to_ci_yaml = ".github/workflows/ci.yaml";
    let file = std::fs::File::open(path_to_ci_yaml).expect("could not open file");
    let contents: serde_yaml::Value =
        serde_yaml::from_reader(file).expect("could not read file contents");
    let mut ci_cmds = contents["jobs"]["runner"]["strategy"]["matrix"]["cmd"]
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
                let mut call = vec!["runner"];
                call.append(cmd);
                let opt = Opt::from_iter(call);
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
                command: Cmd::new_with_env(
                    "cargo",
                    spread![
                        "fmt",
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

fn run_cargo_test(opt: &RunTestsOpt, all_affected_crates: &ModifiedContent) -> Step {
    Step::Multiple {
        name: "cargo test".to_string(),
        steps: crate_manifest_files()
            // Exclude `fuzz` crates, as there are no tests and binaries should not be executed.
            .filter(|path| !is_fuzzing_toml_file(path))
            .map(to_string)
            .filter(|path| all_affected_crates.contains(path))
            .map(|entry| {
                // Manually exclude `oak-introspection-client` for `oak_loader` and `oak_runtime` to
                // avoid compile time errors.
                let features = if entry.contains("oak_loader") {
                    "--features=oak-unsafe,awskms,gcpkms,oak-attestation"
                } else if entry.contains("oak_runtime") {
                    "--features=oak-unsafe,awskms,gcpkms,linear-handles"
                } else {
                    "--all-features"
                };
                let test_run_step = |name| Step::Single {
                    name,
                    command: Cmd::new(
                        "cargo",
                        &[
                            "test",
                            // Compile and test for all features
                            features,
                            &format!("--manifest-path={}", &entry),
                        ],
                    ),
                };
                let target_path = &entry.replace("Cargo.toml", "target");

                // If `cleanup` is enabled, add a cleanup step to remove the generated files. Do
                // this only if `target_path` is a non-empty, valid target path.
                if opt.cleanup && target_path.ends_with("/target") {
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

fn run_cargo_clippy(all_affected_crates: &ModifiedContent) -> Step {
    Step::Multiple {
        name: "cargo clippy".to_string(),
        steps: crate_manifest_files()
            .map(to_string)
            .filter(|path| all_affected_crates.contains(path))
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

fn run_cargo_udeps() -> Step {
    Step::Multiple {
        name: "cargo udeps".to_string(),
        steps: workspace_manifest_files()
            .map(to_string)
            .map(|entry| Step::Single {
                name: entry.clone(),
                command: Cmd::new(
                    "cargo",
                    &[
                        "udeps",
                        &format!("--manifest-path={}", &entry),
                        "--all-targets",
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
        command: Cmd::new("bazel", &["build", "--", "//oak/...:all"]),
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
                "//oak/...:all",
                "//remote_attestation/java/tests/...:all",
                "//oak_functions/client/java/tests/...:all",
            ],
        ),
    }
}
