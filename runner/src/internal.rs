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

pub struct MultipleStatusResult {
    statuses: Vec<Status>,
}

/// The result of a step of execution which may itself be single or multiple.
pub enum StatusResult {
    Single(SingleStatusResult),
    Multiple(MultipleStatusResult),
}

/// The result of executing a `Runnable` step.
pub struct Status {
    name: String,
    status: StatusResult,
}

impl Status {
    pub fn values(&self) -> HashSet<StatusResultValue> {
        match &self.status {
            StatusResult::Single(r) => {
                let mut values = HashSet::new();
                values.insert(r.value.clone());
                values
            }
            StatusResult::Multiple(r) => r.statuses.iter().map(Status::values).flatten().collect(),
        }
    }
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

/// A runnable task, which may be implemented as a single or multiple steps.
pub trait Runnable {
    fn run(&self, opt: &Opt) -> Status;
}

/// Type alias for a boxed, dynamically dispatched `Runnable` instance.
pub type R = Box<dyn Runnable>;

/// Print out a summary of the final status (including subtasks).
pub fn print_all(opt: &Opt, status: &Status) {
    let root = Context::root(&opt);
    print_status(&root, &status);
}

/// Print the provided status to stderr, applying colors to output when possible.
pub fn print_status(context: &Context, status: &Status) {
    let context = context.child(&status.name);
    match &status.status {
        StatusResult::Single(SingleStatusResult {
            value,
            logs,
            command,
        }) => {
            eprintln!("{} ⊢ {}", context.prefix, value);
            if context.opt.commands || context.opt.dry_run {
                eprintln!("{} ⊢ [{}]", context.prefix, command);
            };
            if value == &StatusResultValue::Error || context.opt.logs {
                eprintln!("{} {}", context.prefix, "╔════════════════════════".blue());
                for line in logs.lines() {
                    eprintln!("{} {} {}", context.prefix, "║".blue(), line);
                }
                eprintln!("{} {}", context.prefix, "╚════════════════════════".blue());
            }
        }
        StatusResult::Multiple(MultipleStatusResult { statuses }) => {
            eprintln!("{} {{", context.prefix);
            for status in statuses.iter() {
                print_status(&context, status);
            }
            eprintln!(
                "{} }} ⊢ {}",
                context.prefix,
                values_to_string(status.values())
            );
        }
    }
}

/// A step executor, which pretty prints the current nesting level, and allows executing commands
/// and reporting their result.
struct Step {
    name: String,
    executable: String,
    args: Vec<String>,
}

impl Step {
    /// Create the root step executor, of which there should only be one.
    fn new(name: &str, executable: &str, args: &[&str]) -> Self {
        Step {
            name: name.to_string(),
            executable: executable.to_string(),
            args: args.iter().cloned().map(|s| s.to_string()).collect(),
        }
    }
}

pub fn step(name: &str, executable: &str, args: &[&str]) -> R {
    Box::new(Step::new(name, executable, args))
}

impl Runnable for Step {
    /// Run the provided command, printing a status message with the current prefix.
    /// TODO: Add ability to run commands in parallel.
    /// TODO: Return one of three results: pass, fail, or internal error (e.g. if the binary to run
    /// was not found).
    fn run(&self, opt: &Opt) -> Status {
        // TODO: Measure and print elapsed time.
        // TODO: Add dry-run mode that only prints the commands but does not actually run them.
        std::io::stderr().flush().expect("could not flush stderr");
        let mut cmd = Command::new(&self.executable);
        cmd.args(&self.args);
        let command_string = format!("{:?}", cmd);
        let status = if opt.dry_run {
            StatusResult::Single(SingleStatusResult {
                value: StatusResultValue::Skipped,
                command: command_string,
                logs: "".to_string(),
            })
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
                StatusResult::Single(SingleStatusResult {
                    value: StatusResultValue::Ok,
                    command: command_string,
                    logs,
                })
            } else {
                StatusResult::Single(SingleStatusResult {
                    value: StatusResultValue::Error,
                    command: command_string,
                    logs,
                })
            }
        };
        Status {
            name: self.name.clone(),
            status,
        }
    }
}

struct Sequence {
    name: String,
    entries: Vec<R>,
}

impl Sequence {
    fn new<E>(name: &str, entries: E) -> Self
    where
        E: IntoIterator<Item = R>,
    {
        Sequence {
            name: name.to_string(),
            entries: entries.into_iter().collect(),
        }
    }
}

pub fn sequence<E>(name: &str, entries: E) -> R
where
    E: IntoIterator<Item = R>,
{
    Box::new(Sequence::new(name, entries))
}

impl Runnable for Sequence {
    fn run(&self, opt: &Opt) -> Status {
        let statuses = self.entries.iter().map(|entry| entry.run(opt)).collect();
        Status {
            name: self.name.clone(),
            status: StatusResult::Multiple(MultipleStatusResult { statuses }),
        }
    }
}
