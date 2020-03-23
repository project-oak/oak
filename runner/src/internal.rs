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

use colored::*;
use std::collections::HashSet;
use std::io::Write;
use std::process::Command;
use std::time::Instant;
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
pub struct Opt {
    #[structopt(long)]
    dry_run: bool,
    #[structopt(long)]
    commands: bool,
    #[structopt(long)]
    logs: bool,
}

/// Encapsulates all the local state relative to a step, and is propagated to child steps.
pub struct Context {
    opt: Opt,
    prefix: String,
}

impl Context {
    pub fn root(opt: &Opt) -> Self {
        Context {
            opt: opt.clone(),
            prefix: "".to_string(),
        }
    }

    fn child(&self, prefix: &str) -> Self {
        Context {
            opt: self.opt.clone(),
            prefix: format!("{} ➡ {}", self.prefix, prefix),
        }
    }
}

/// The outcome of an individual step of execution.
#[derive(PartialEq, Eq, Clone, Hash)]
pub enum StatusResultValue {
    Ok,
    Error,
    Skipped,
}

impl std::fmt::Display for StatusResultValue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            StatusResultValue::Ok => write!(f, "{}", "OK".bold().bright_green()),
            StatusResultValue::Error => write!(f, "{}", "ERROR".bold().bright_red()),
            StatusResultValue::Skipped => write!(f, "{}", "SKIPPED".bold().bright_yellow()),
        }
    }
}

pub struct SingleStatusResult {
    value: StatusResultValue,
    command: String,
    logs: String,
}

/// An execution step, which may be a single (dynamically dispatched) `Runnable`, or a collection of
/// sub-steps.
pub enum Step {
    Single {
        name: String,
        runnable: Box<dyn Runnable>,
    },
    Multiple {
        name: String,
        steps: Vec<Step>,
    },
}

fn values_to_string<T>(values: T) -> String
where
    T: IntoIterator,
    T::Item: std::fmt::Display,
{
    format!(
        "[{}]",
        values
            .into_iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(",")
    )
}

/// A runnable task which produces a single result.
pub trait Runnable {
    fn run(&self, opt: &Opt) -> SingleStatusResult;
}

/// Run the provided step, printing out information about the execution, and returning a set of
/// status results from the single or multiple steps that were executed.
pub fn run_step(context: &Context, step: &Step) -> HashSet<StatusResultValue> {
    match step {
        Step::Single { name, runnable } => {
            let context = context.child(name);
            // Print three dots to indicate that a command is running, but no new line. The first
            // log line below will complete the line.
            eprint!("{} ... ", context.prefix);

            let start = Instant::now();
            let status = runnable.run(&context.opt);
            let end = Instant::now();
            let elapsed = end.duration_since(start);

            eprintln!("{} [{:.0?}]", status.value, elapsed);
            if context.opt.commands || context.opt.dry_run {
                eprintln!("{} ⊢ [{}]", context.prefix, status.command);
            };
            if status.value == StatusResultValue::Error || context.opt.logs {
                eprintln!("{} {}", context.prefix, "╔════════════════════════".blue());
                for line in status.logs.lines() {
                    eprintln!("{} {} {}", context.prefix, "║".blue(), line);
                }
                eprintln!("{} {}", context.prefix, "╚════════════════════════".blue());
            }
            let mut values = HashSet::new();
            values.insert(status.value);
            values
        }
        Step::Multiple { name, steps } => {
            let context = context.child(name);
            eprintln!("{} {{", context.prefix);
            let start = Instant::now();
            let values = steps
                .iter()
                .map(|step| run_step(&context, step))
                .flatten()
                .collect();
            let end = Instant::now();
            let elapsed = end.duration_since(start);
            eprintln!(
                "{} }} ⊢ {} [{:.0?}]",
                context.prefix,
                values_to_string(&values),
                elapsed
            );
            values
        }
    }
}

/// A single command that implements the `Runnable` trait.
struct Cmd {
    executable: String,
    args: Vec<String>,
}

impl Cmd {
    fn new(executable: &str, args: &[&str]) -> Self {
        Cmd {
            executable: executable.to_string(),
            args: args.iter().cloned().map(|s| s.to_string()).collect(),
        }
    }
}

/// Convenience constructor for a boxed `Cmd`.
pub fn cmd(executable: &str, args: &[&str]) -> Box<dyn Runnable> {
    Box::new(Cmd::new(executable, args))
}

impl Runnable for Cmd {
    /// Run the provided command, printing a status message with the current prefix.
    /// TODO(#396): Add ability to run commands in parallel.
    /// TODO(#396): Return one of three results: pass, fail, or internal error (e.g. if the binary
    /// to run was not found).
    fn run(&self, opt: &Opt) -> SingleStatusResult {
        // TODO(#396): Measure and print elapsed time.
        // TODO(#396): Add dry-run mode that only prints the commands but does not actually run
        // them.
        std::io::stderr().flush().expect("could not flush stderr");
        let mut cmd = Command::new(&self.executable);
        cmd.args(&self.args);
        let command_string = format!("{:?}", cmd);
        if opt.dry_run {
            SingleStatusResult {
                value: StatusResultValue::Skipped,
                command: command_string,
                logs: "".to_string(),
            }
        } else {
            let child = cmd
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .expect("could not spawn command");
            let output = child
                .wait_with_output()
                .expect("could not wait for command to terminate");
            let logs = format!(
                "\n{}\n----\n{}\n",
                std::str::from_utf8(&output.stdout).expect("could not parse command output"),
                std::str::from_utf8(&output.stderr).expect("could not parse command output"),
            );
            if output.status.success() {
                SingleStatusResult {
                    value: StatusResultValue::Ok,
                    command: command_string,
                    logs,
                }
            } else {
                SingleStatusResult {
                    value: StatusResultValue::Error,
                    command: command_string,
                    logs,
                }
            }
        }
    }
}
