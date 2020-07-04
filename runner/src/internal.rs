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
use futures::future::BoxFuture;
use futures_util::future::FutureExt;
use std::{
    collections::{HashMap, HashSet},
    future::Future,
    io::{Read, Write},
    sync::{Arc, Mutex},
    time::Instant,
};
use structopt::StructOpt;
use tokio::io::AsyncReadExt;

#[derive(StructOpt, Clone)]
pub struct Opt {
    #[structopt(long, help = "do not execute commands")]
    dry_run: bool,
    #[structopt(long, help = "re-run commands on file changes")]
    pub watch: bool,
    #[structopt(long, help = "print commands")]
    commands: bool,
    #[structopt(long, help = "show logs of commands")]
    logs: bool,
    #[structopt(subcommand)]
    pub cmd: Command,
}

#[derive(StructOpt, Clone)]
pub enum Command {
    RunExamples(RunExamples),
    BuildServer(BuildServer),
    Format,
    CheckFormat,
    RunTests,
    RunCi,
}

#[derive(StructOpt, Clone)]
pub struct RunExamples {
    #[structopt(
        long,
        help = "application variant: [rust, cpp]",
        default_value = "rust"
    )]
    pub application_variant: String,
    // TODO(#396): Clarify the name and type of this, currently it is not very intuitive.
    #[structopt(
        long,
        help = "name of a single example to run; if unset, run all the examples"
    )]
    pub example_name: Option<String>,
    #[structopt(flatten)]
    pub build_server: BuildServer,
    #[structopt(long, help = "run server [default: true]")]
    pub run_server: Option<bool>,
    #[structopt(long, help = "run clients [default: true]")]
    pub run_clients: Option<bool>,
    #[structopt(long, help = "additional arguments to pass to clients")]
    pub client_additional_args: Vec<String>,
    #[structopt(long, help = "additional arguments to pass to server")]
    pub server_additional_args: Vec<String>,
    #[structopt(long, help = "build a Docker image for the examples")]
    pub build_docker: bool,
}

#[derive(StructOpt, Clone)]
pub struct BuildServer {
    #[structopt(long, help = "server variant: [base, logless]", default_value = "base")]
    pub server_variant: String,
    #[structopt(
        long,
        help = "rust toolchain override to use for the server compilation [e.g. stable, nightly, stage2]"
    )]
    pub server_rust_toolchain: Option<String>,
    #[structopt(
        long,
        help = "rust target to use for the server compilation [e.g. x86_64-unknown-linux-gnu, x86_64-unknown-linux-musl]",
        default_value = "x86_64-unknown-linux-musl"
    )]
    pub server_rust_target: String,
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
            prefix: format!("{} ❯ {}", self.prefix, prefix),
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

#[derive(Clone)]
pub struct SingleStatusResult {
    pub value: StatusResultValue,
    pub logs: String,
}

/// An execution step, which may be a single `Runnable`, or a collection of sub-steps.
pub enum Step {
    Single {
        name: String,
        command: Box<dyn Runnable>,
    },
    Multiple {
        name: String,
        steps: Vec<Step>,
    },
    WithBackground {
        name: String,
        background: Box<dyn Runnable>,
        foreground: Box<Step>,
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

/// Run the provided step, printing out information about the execution, and returning a set of
/// status results from the single or multiple steps that were executed.
pub fn run_step<'a>(
    context: &'a Context,
    step: &'a Step,
) -> BoxFuture<'a, HashSet<StatusResultValue>> {
    async move {
        match step {
            Step::Single { name, command } => {
                let context = context.child(name);

                let start = Instant::now();
                let mut running = command.run(&context.opt);

                if context.opt.commands || context.opt.dry_run {
                    eprintln!("{} ⊢ [{}] ... ", context.prefix, running);
                }

                eprint!("{} ⊢ ", context.prefix);
                let status = running.wait(&context.opt).await;
                let end = Instant::now();
                let elapsed = end.duration_since(start);
                eprintln!("{} [{:.0?}]", status.value, elapsed);

                if (status.value == StatusResultValue::Error || context.opt.logs)
                    && !status.logs.is_empty()
                {
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
                let values =
                    futures::future::join_all(steps.iter().map(|step| run_step(&context, step)))
                        .await
                        .iter()
                        .flatten()
                        .cloned()
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
            Step::WithBackground {
                name,
                background,
                foreground,
            } => {
                let context = context.child(name);
                eprintln!("{} {{", context.prefix);

                let mut running_background = background.run(&context.opt);
                let background_command = if context.opt.commands || context.opt.dry_run {
                    format!("[{}]", running_background)
                } else {
                    "".to_string()
                };
                eprintln!(
                    "{} ⊢ {} (background) ...",
                    context.prefix, background_command
                );

                // Small delay to make it more likely that the background process started.
                std::thread::sleep(std::time::Duration::from_millis(2_000));

                let values = run_step(&context, foreground).await;

                running_background.kill();
                eprintln!("{} ⊢ {} (waiting)", context.prefix, background_command,);
                let background_status = running_background.wait(&context.opt).await;
                eprintln!(
                    "{} ⊢ {} (finished) {}",
                    context.prefix, background_command, background_status.value
                );
                if (background_status.value == StatusResultValue::Error
                    || values.contains(&StatusResultValue::Error)
                    || context.opt.logs)
                    && !background_status.logs.is_empty()
                {
                    eprintln!("{} {}", context.prefix, "╔════════════════════════".blue());
                    for line in background_status.logs.lines() {
                        eprintln!("{} {} {}", context.prefix, "║".blue(), line);
                    }
                    eprintln!("{} {}", context.prefix, "╚════════════════════════".blue());
                }

                values
            }
        }
    }
    .boxed()
}

/// A single command.
#[derive(Clone)]
pub struct Cmd {
    executable: String,
    args: Vec<String>,
    env: HashMap<String, String>,
}

impl Cmd {
    pub fn new<I, S>(executable: &str, args: I) -> Box<Self>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        Box::new(Cmd {
            executable: executable.to_string(),
            args: args.into_iter().map(|s| s.as_ref().to_string()).collect(),
            env: HashMap::new(),
        })
    }

    pub fn new_with_env<I, S>(executable: &str, args: I, env: &HashMap<String, String>) -> Box<Self>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        Box::new(Cmd {
            executable: executable.to_string(),
            args: args.into_iter().map(|s| s.as_ref().to_string()).collect(),
            env: env.clone(),
        })
    }
}

impl Runnable for Cmd {
    /// Run the provided command, printing a status message with the current prefix.
    /// TODO(#396): Return one of three results: pass, fail, or internal error (e.g. if the binary
    /// to run was not found).
    fn run(&self, opt: &Opt) -> Box<dyn Running> {
        std::io::stderr().flush().expect("could not flush stderr");
        let mut cmd = tokio::process::Command::new(&self.executable);
        cmd.args(&self.args);

        // Clear the parent environment. Only the variables explicitly passed below are going to be
        // available to the command, to avoid accidentally depending on extraneous ones.
        cmd.env_clear();

        // General variables.
        cmd.env("HOME", std::env::var("HOME").unwrap());
        cmd.env("PATH", std::env::var("PATH").unwrap());
        if let Ok(v) = std::env::var("USER") {
            cmd.env("USER", v);
        }

        // Python variables.
        if let Ok(v) = std::env::var("PYTHONPATH") {
            cmd.env("PYTHONPATH", v);
        }

        // Rust compilation variables.
        if let Ok(v) = std::env::var("RUSTUP_HOME") {
            cmd.env("RUSTUP_HOME", v);
        }
        if let Ok(v) = std::env::var("CARGO_HOME") {
            cmd.env("CARGO_HOME", v);
        }

        // Rust runtime variables.
        cmd.env(
            "RUST_LOG",
            std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string()),
        );
        cmd.env("RUST_BACKTRACE", "1");

        // Emscripten variables.
        if let Ok(v) = std::env::var("EMSDK") {
            cmd.env("EMSDK", v);
        }
        if let Ok(v) = std::env::var("EM_CACHE") {
            cmd.env("EM_CACHE", v);
        }
        if let Ok(v) = std::env::var("EM_CONFIG") {
            cmd.env("EM_CONFIG", v);
        }

        cmd.envs(&self.env);

        let command_string = format!("{:?}", cmd);
        if opt.dry_run {
            Box::new(RunningCmd {
                command: command_string,
                process: None,
                stdout: Default::default(),
                stderr: Default::default(),
            })
        } else {
            // If the `logs` flag is enabled, inherit stdout and stderr from the main runner
            // process.
            let stdout = if opt.logs {
                std::process::Stdio::inherit()
            } else {
                std::process::Stdio::piped()
            };
            let stderr = if opt.logs {
                std::process::Stdio::inherit()
            } else {
                std::process::Stdio::piped()
            };
            let mut child = cmd
                .stdout(stdout)
                .stderr(stderr)
                .spawn()
                .expect("could not spawn command");

            let stdout_logs = if opt.logs { None } else { child.stdout.take() };
            let stderr_logs = if opt.logs { None } else { child.stderr.take() };

            Box::new(RunningCmd {
                command: command_string,
                process: Some(child),
                stdout: stdout_logs,
                stderr: stderr_logs,
            })
        }
    }
}

/// Reads a stream in a separate thread, to avoid internal pipe buffers filling and causing a
/// deadlock.
fn read_background<T: Read + Send + 'static>(mut r: T) -> Arc<Mutex<String>> {
    let buf = Arc::new(Mutex::new(String::new()));
    let buf_2 = buf.clone();
    std::thread::spawn(move || {
        let mut s = buf_2.lock().expect("could not take logs lock");
        r.read_to_string(&mut s).expect("could not read logs");
    });
    buf
}

/// An instance of a running command.
pub struct RunningCmd {
    command: String,
    process: Option<tokio::process::Child>,
    stdout: Option<tokio::process::ChildStdout>,
    stderr: Option<tokio::process::ChildStderr>,
}

impl Running for RunningCmd {
    /// Forces the running command to stop. Equivalent to sending `SIGINT`.
    fn kill(&mut self) {
        if let Some(ref mut child) = self.process {
            // TODO(#396): Send increasingly stronger signals if the process fails to terminate
            // within a given amount of time.
            let pid = nix::unistd::Pid::from_raw(child.id() as i32);
            nix::sys::signal::kill(pid, nix::sys::signal::Signal::SIGINT)
                .expect("could not kill process");
        }
    }

    /// Waits for the running command to spontaneously terminate.
    fn wait(&mut self, _opt: &Opt) -> BoxFuture<SingleStatusResult> {
        async move {
            let child = match self.process.take() {
                Some(child) => child,
                None => {
                    return SingleStatusResult {
                        logs: "".to_string(),
                        value: StatusResultValue::Skipped,
                    }
                }
            };

            let exit_status = child.await.expect("could not get exit status");

            let mut logs = String::new();
            {
                let mut stdout = String::new();
                self.stdout
                    .take()
                    .expect("could not read stdout")
                    .read_to_string(&mut stdout)
                    .await;
                if !stdout.is_empty() {
                    logs += &format!("════╡ stdout ╞════\n{}", stdout);
                }
            }
            {
                let mut stderr = String::new();
                self.stderr
                    .take()
                    .expect("could not read stderr")
                    .read_to_string(&mut stderr)
                    .await;
                if !stderr.is_empty() {
                    logs += &format!("════╡ stderr ╞════\n{}", stderr);
                }
            }

            if exit_status.success() {
                SingleStatusResult {
                    value: StatusResultValue::Ok,
                    logs,
                }
            } else {
                SingleStatusResult {
                    value: StatusResultValue::Error,
                    logs,
                }
            }
        }
        .boxed()
    }
}

/// Similar to the `vec!` macro, but also allows a "spread" operator syntax (`...`) to inline and
/// expand nested iterable values.
///
/// See https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Spread_syntax.
#[macro_export]
macro_rules! spread [
    // Empty case.
    () => (
        vec![].iter()
    );
    // Spread value base case.
    (...$vv:expr) => (
        $vv.iter()
    );
    // Spread value recursive case.
    (...$vv:expr, $($rest:tt)*) => (
        $vv.iter().chain( spread![$($rest)*] )
    );
    // Single value base case.
    ($v:expr) => (
        vec![$v].iter()
    );
    // Single value recursive case.
    ($v:expr, $($rest:tt)*) => (
        vec![$v].iter().chain( spread![$($rest)*] )
    );
];

#[test]
fn test_spread() {
    assert_eq!(vec![1], spread![1].cloned().collect::<Vec<i32>>());
    assert_eq!(vec![1, 2], spread![1, 2].cloned().collect::<Vec<i32>>());
    assert_eq!(
        vec![1, 2, 3, 4],
        spread![1, 2, 3, 4].cloned().collect::<Vec<i32>>()
    );
    assert_eq!(
        vec![1, 2, 3, 4],
        spread![...vec![1, 2], 3, 4].cloned().collect::<Vec<i32>>()
    );
    assert_eq!(
        vec![1, 2, 3, 4],
        spread![1, ...vec![2, 3], 4].cloned().collect::<Vec<i32>>()
    );
    assert_eq!(
        vec![1, 2, 3, 4],
        spread![1, 2, ...vec![3, 4]].cloned().collect::<Vec<i32>>()
    );
    assert_eq!(
        vec![1, 2, 3, 4],
        spread![...vec![1, 2], ...vec![3, 4]]
            .cloned()
            .collect::<Vec<i32>>()
    );
    assert_eq!(
        vec![1, 2, 3, 4],
        spread![...vec![1, 2, 3, 4]].cloned().collect::<Vec<i32>>()
    );

    assert_eq!(
        vec!["foo", "bar"],
        spread!["foo", "bar"].cloned().collect::<Vec<_>>()
    );
}

impl std::fmt::Display for RunningCmd {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.command)
    }
}

/// An implementation of [`Running`] that immediately returns a pre-determined
/// [`SingleStatusResult`] value.
pub struct ImmediateResult {
    pub result: SingleStatusResult,
}

impl Running for ImmediateResult {
    fn kill(&mut self) {}
    fn wait(&mut self, _opt: &Opt) -> BoxFuture<SingleStatusResult> {
        Box::pin(futures::future::ready(self.result.clone()))
    }
}

impl std::fmt::Display for ImmediateResult {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "n/a")
    }
}

pub trait Runnable: Sync {
    fn run(&self, opt: &Opt) -> Box<dyn Running>;
}

pub trait Running: std::fmt::Display + Send {
    fn kill(&mut self);
    fn wait(&mut self, opt: &Opt) -> BoxFuture<SingleStatusResult>;
}
