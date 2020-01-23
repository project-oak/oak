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
    pub fn root(opt: Opt) -> Self {
        Context {
            opt,
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

pub trait Runnable {
    fn run(&self, context: &Context);
}

/// Type alias for a boxed, dynamically dispatched `Runnable` instance.
pub type R = Box<dyn Runnable>;

/// A step executor, which pretty prints the current nesting level, and allows executing commands
/// and reporting their result.
pub struct Step {
    name: String,
    executable: String,
    args: Vec<String>,
}

impl Step {
    /// Create the root step executor, of which there should only be one.
    pub fn new(name: &str, executable: &str, args: &[&str]) -> R {
        Box::new(Step {
            name: name.to_string(),
            executable: executable.to_string(),
            args: args.iter().cloned().map(|s| s.to_string()).collect(),
        })
    }
}

impl Runnable for Step {
    /// Run the provided command, printing a status message with the current prefix.
    /// TODO: Add ability to run commands in parallel.
    /// TODO: Return one of three results: pass, fail, or internal error (e.g. if the binary to run
    /// was not found).
    fn run(&self, context: &Context) {
        let context = context.child(&self.name);
        // TODO: Measure and print elapsed time.
        // TODO: Add dry-run mode that only prints the commands but does not actually run them.
        eprint!("{} ⊢ ", context.prefix);
        std::io::stderr().flush().expect("could not flush stderr");
        let mut cmd = Command::new(&self.executable);
        cmd.args(&self.args);
        // `dry_run` implies `commands`, otherwise there is not much to see in the output.
        if context.opt.commands || context.opt.dry_run {
            eprint!("[{:?}] ", cmd);
        }
        if context.opt.dry_run {
            eprintln!("{}", "SKIPPED".bold().bright_yellow());
        } else {
            let child = cmd
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .expect("could not spawn command");
            let output = child
                .wait_with_output()
                .expect("could not wait for command to terminate");
            if output.status.success() {
                eprintln!("{}", "OK".bold().bright_green());
            } else {
                eprintln!("{} ({})", "ERROR".bold().bright_red(), output.status);
            }
            if !output.status.success() || context.opt.logs {
                eprintln!(
                    "⬇⬇⬇⬇\n{}\n----\n{}\n⬆⬆⬆⬆",
                    std::str::from_utf8(&output.stdout).expect("could not parse command output"),
                    std::str::from_utf8(&output.stderr).expect("could not parse command output"),
                );
            }
        }
    }
}

pub struct Sequence {
    name: String,
    entries: Vec<R>,
}

impl Sequence {
    pub fn new<E>(name: &str, entries: E) -> R
    where
        E: IntoIterator<Item = R>,
    {
        Box::new(Sequence {
            name: name.to_string(),
            entries: entries.into_iter().collect(),
        })
    }
}

impl Runnable for Sequence {
    fn run(&self, context: &Context) {
        let context = context.child(&self.name);
        eprintln!("{} {{", context.prefix);
        for entry in &self.entries {
            entry.run(&context);
        }
        eprintln!("{} }}", context.prefix);
    }
}
