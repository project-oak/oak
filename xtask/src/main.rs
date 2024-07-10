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

//! A utility binary to run tests and orchestrate examples and other tools
//! within the repository, for local development and CI.
//!
//! To invoke, run the following command from the root of the repository:
//!
//! ```
//! cargo run --manifest-path=xtask/Cargo.toml
//! ```

#![feature(async_closure)]

use std::path::{Path, PathBuf};

use clap::{CommandFactory, Parser};
use colored::*;
use xtask::{
    files::*,
    internal::{self, *},
};

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
        // TODO(#396): Add support for running individual commands via command line
        // flags.
        let remaining_steps = steps.len();
        run_step(&Context::root(&opt), steps, Status::new(remaining_steps)).await
    };

    // This is a crude way of killing any potentially running process when receiving
    // a Ctrl-C signal. We collect all process IDs in the `PROCESSES` variable,
    // regardless of whether they have already been terminated, and we try to
    // kill all of them when receiving the signal.
    tokio::spawn(async {
        tokio::signal::ctrl_c().await.expect("couldn't wait for signal");
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
        Command::RunTests => run_tests(),
        Command::RunCargoClippy => run_cargo_clippy(),
        Command::Completion(ref opt) => run_completion(opt),
        Command::RunCargoDeny => run_cargo_deny(),
        Command::RunCargoUdeps => run_cargo_udeps(),
    }
}

fn cleanup() {
    eprintln!();
    eprintln!(
        "{}",
        "signal or panic received, killing outstanding processes".bright_white().on_red()
    );
    for pid in xtask::PROCESSES.lock().expect("couldn't acquire processes lock").iter() {
        // We intentionally don't print anything here as it may obscure more interesting
        // results from the current execution.
        internal::kill_process(*pid);
    }
}

fn run_tests() -> Step {
    Step::Multiple {
        name: "tests".to_string(),
        steps: vec![run_cargo_tests(&RunTestsOpt { cleanup: false })],
    }
}

fn run_cargo_tests(opt: &RunTestsOpt) -> Step {
    Step::Multiple {
        name: "cargo tests".to_string(),
        steps: vec![run_cargo_test(opt), run_cargo_doc()],
    }
}

fn run_completion(completion: &Completion) -> Step {
    let mut file = std::fs::File::create(completion.file_name.clone()).expect("file not created");
    clap_complete::generate(clap_complete::Shell::Bash, &mut Opt::command(), "xtask", &mut file);

    // Return an empty step. Otherwise we cannot call run_completion from match_cmd.
    Step::Multiple { name: "cargo completion".to_string(), steps: vec![] }
}

fn run_cargo_test(opt: &RunTestsOpt) -> Step {
    Step::Multiple {
        name: "cargo test".to_string(),
        steps: crate_manifest_files()
            .map(|entry| {
                // Run `cargo test` in the directory of the crate, not the top-level directory.
                // This is needed as otherwise any crate-specific `.cargo/config.toml` files
                // would be ignored. If a crate does not have a config file,
                // Cargo will just backtrack up the tree and pick up the
                // `.cargo/config.toml` file from the root directory.
                let test_run_step = |name| Step::Single {
                    name,
                    command: Cmd::new_in_dir(
                        "cargo",
                        [
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
                                    ["-rf", entry.with_file_name("target").to_str().unwrap()],
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

fn run_cargo_doc() -> Step {
    Step::Multiple {
        name: "cargo doc".to_string(),
        steps: crate_manifest_files()
            .map(to_string)
            .map(|entry| {
                let mut path = PathBuf::from(entry);
                path.pop();
                let path = to_string(path).replace("./", "");
                Step::Single {
                    name: path.clone(),
                    command: Cmd::new("bash", ["./scripts/check_docs", &path]),
                }
            })
            .collect(),
    }
}

fn run_cargo_clippy() -> Step {
    for m in crate_manifest_files() {
        println!("MANIFEST {m:?}")
    }
    Step::Multiple {
        name: "cargo clippy".to_string(),
        steps: crate_manifest_files()
            .map(|entry| Step::Single {
                name: entry.to_str().unwrap().to_string(),
                command: Cmd::new_in_dir(
                    "cargo",
                    [
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
                    ["deny", &format!("--manifest-path={}", &entry), "check"],
                ),
            })
            .collect(),
    }
}

fn run_cargo_udeps() -> Step {
    Step::Multiple {
        name: "cargo udeps".to_string(),
        steps: workspace_manifest_files()
            // TODO(#4129): Remove when cargo-udeps supports build-std.
            .filter(|path| {
                path != Path::new("./stage0_bin/Cargo.toml")
                    && path != Path::new("./oak_restricted_kernel_wrapper/Cargo.toml")
            })
            .map(|entry| Step::Single {
                name: entry.to_str().unwrap().to_string(),
                command: Cmd::new_in_dir(
                    "cargo",
                    [
                        "udeps",
                        &format!(
                            "--manifest-path={}",
                            entry.file_name().unwrap().to_str().unwrap()
                        ),
                        "--all-targets",
                        // The depinfo backend seems much faster and precise.
                        "--backend=depinfo",
                        "--workspace",
                    ],
                    entry.parent().unwrap(),
                ),
            })
            .collect(),
    }
}
