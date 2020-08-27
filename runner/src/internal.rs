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

use async_recursion::async_recursion;
use async_trait::async_trait;
use colored::*;
use std::{
    collections::{HashMap, HashSet},
    time::Instant,
};
use structopt::StructOpt;
use tokio::io::{empty, AsyncRead, AsyncReadExt};

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
    RunTestsTsan,
    RunCi,
    #[structopt(about = "generate bash completion script to stdout")]
    Completion,
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
    pub build_client: BuildClient,
    #[structopt(flatten)]
    pub build_server: BuildServer,
    #[structopt(long, help = "run server [default: true]")]
    pub run_server: Option<bool>,
    #[structopt(long, help = "additional arguments to pass to clients")]
    pub client_additional_args: Vec<String>,
    #[structopt(long, help = "additional arguments to pass to server")]
    pub server_additional_args: Vec<String>,
    #[structopt(long, help = "build a Docker image for the examples")]
    pub build_docker: bool,
}

#[derive(StructOpt, Clone)]
pub struct BuildClient {
    #[structopt(
        long,
        help = "client variant: [all, rust, cpp, go, nodejs, none] [default: all]",
        default_value = "all"
    )]
    pub client_variant: String,
    #[structopt(
        long,
        help = "rust toolchain override to use for the client compilation [e.g. stable, nightly, stage2]"
    )]
    pub client_rust_toolchain: Option<String>,
    #[structopt(
        long,
        help = "rust target to use for the client compilation [e.g. x86_64-unknown-linux-gnu, x86_64-unknown-linux-musl, x86_64-apple-darwin]"
    )]
    pub client_rust_target: Option<String>,
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
        help = "rust target to use for the server compilation [e.g. x86_64-unknown-linux-gnu, x86_64-unknown-linux-musl, x86_64-apple-darwin]"
    )]
    pub server_rust_target: Option<String>,
    #[structopt(long, help = "produce coverage report")]
    pub coverage: bool,
}

/// A construct to keep track of the status of the execution. It only cares about the top-level
/// steps.
#[derive(Clone)]
pub struct Status {
    error: usize,
    ok: usize,
    remaining: usize,
}

impl Status {
    pub fn new(remaining: usize) -> Self {
        Status {
            error: 0,
            ok: 0,
            remaining,
        }
    }

    /// Guarantees that the `error`, `ok`, and `remaining` counts are updated only after the
    /// completions of each top-level step.
    fn update(&mut self, context: &Context, step_has_error: bool) {
        // Update the status with results from the step, only if it is a top-level step.
        if context.depth() == 1 {
            self.remaining -= 1;
            // We only care about pass (`ok`) and fail (`error`). If an entire step is skipped, we
            // count it as a passed step.
            if step_has_error {
                self.error += 1;
            } else {
                self.ok += 1;
            }
        }
    }
}

/// Formats the status as `E:<error-count>,O:<ok-count>,R:<remaining-count>`, suitable for
/// annotating the log lines.
impl std::fmt::Display for Status {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "E:{},O:{},R:{}", self.error, self.ok, self.remaining)
    }
}

/// Encapsulates all the local state relative to a step, and is propagated to child steps.
pub struct Context {
    opt: Opt,
    prefix: Vec<String>,
}

impl Context {
    pub fn root(opt: &Opt) -> Self {
        Context {
            opt: opt.clone(),
            prefix: vec![],
        }
    }

    fn child(&self, name: &str) -> Self {
        let mut prefix = self.prefix.clone();
        prefix.push(name.to_string());
        Context {
            opt: self.opt.clone(),
            prefix,
        }
    }

    fn depth(&self) -> usize {
        self.prefix.len()
    }
}

impl std::fmt::Display for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.prefix.join(" ❯ "))
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

impl Step {
    /// Returns the number of top-level steps or commands. The number of sub-steps is not
    /// recursively accumulated in the returned length.
    pub fn len(&self) -> usize {
        match self {
            Step::Single {
                name: _,
                command: _,
            } => 1,
            Step::Multiple { name: _, steps: s } => s.len(),
            Step::WithBackground {
                name: _,
                background: _,
                foreground: f,
            } => f.len(),
        }
    }
}

pub struct StepResult {
    pub values: HashSet<StatusResultValue>,
    pub failed_steps_prefixes: Vec<String>,
}

impl StepResult {
    fn new() -> Self {
        Self {
            values: HashSet::new(),
            failed_steps_prefixes: vec![],
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

/// Run the provided step, printing out information about the execution, and returning a set of
/// status results from the single or multiple steps that were executed.
#[async_recursion]
pub async fn run_step(context: &Context, step: Step, mut run_status: Status) -> StepResult {
    let mut step_result = StepResult::new();
    let now = chrono::Utc::now();
    let time_of_day = now.format("%H:%M:%S");
    match step {
        Step::Single { name, command } => {
            let context = context.child(&name);

            let start = Instant::now();

            if context.opt.commands || context.opt.dry_run {
                eprintln!(
                    "[{}; {}]: {} ⊢ [{}] ... ",
                    time_of_day,
                    run_status,
                    context,
                    command.description().blue()
                );
            }

            eprint!("[{}; {}]: {} ⊢ ", time_of_day, run_status, context);
            let status = command.run(&context.opt).result().await;
            let end = Instant::now();
            let elapsed = end.duration_since(start);
            eprintln!("{} [{:.0?}]", status.value, elapsed);

            let step_failed = status.value == StatusResultValue::Error;
            if (step_failed || context.opt.logs) && !status.logs.is_empty() {
                eprintln!("{} {}", context, "╔════════════════════════".blue());
                for line in status.logs.lines() {
                    eprintln!("{} {} {}", context, "║".blue(), line);
                }
                eprintln!("{} {}", context, "╚════════════════════════".blue());
                step_result
                    .failed_steps_prefixes
                    .push(format!("{}", context));
            }
            step_result.values.insert(status.value);
            run_status.update(&context, step_failed);
        }
        Step::Multiple { name, steps } => {
            let context = context.child(&name);
            eprintln!("[{}; {}]: {} {{", time_of_day, run_status, context);
            let start = Instant::now();
            for step in steps {
                let mut result = run_step(&context, step, run_status.clone()).await;
                step_result.values = step_result.values.union(&result.values).cloned().collect();
                step_result
                    .failed_steps_prefixes
                    .append(&mut result.failed_steps_prefixes);
                run_status.update(&context, result.values.contains(&StatusResultValue::Error));
            }
            let end = Instant::now();
            let elapsed = end.duration_since(start);
            eprintln!(
                "[{}; {}]: {} }} ⊢ {} [{:.0?}]",
                time_of_day,
                run_status,
                context,
                values_to_string(&step_result.values),
                elapsed
            );
        }
        Step::WithBackground {
            name,
            background,
            foreground,
        } => {
            let context = context.child(&name);
            eprintln!("[{}; {}]: {} {{", time_of_day, run_status, context);

            let background_command = if context.opt.commands || context.opt.dry_run {
                format!("[{}]", background.description().blue())
            } else {
                "".to_string()
            };
            eprintln!(
                "[{}; {}]: {} ⊢ {} (background) ...",
                time_of_day, run_status, context, background_command
            );

            let mut running_background = background.run(&context.opt);

            // Small delay to make it more likely that the background process started.
            std::thread::sleep(std::time::Duration::from_millis(6_000));

            async fn read_to_end<A: AsyncRead + Unpin>(mut io: A) -> Vec<u8> {
                let mut buf = Vec::new();
                io.read_to_end(&mut buf)
                    .await
                    .expect("could not read from future");
                buf
            }

            let background_stdout_future = tokio::spawn(read_to_end(running_background.stdout()));
            let background_stderr_future = tokio::spawn(read_to_end(running_background.stderr()));

            let mut foreground_result = run_step(&context, *foreground, run_status.clone()).await;

            // TODO(#396): If the background task was already spontaneously terminated by now, it is
            // probably a sign that something went wrong, so we should return an error.
            running_background.kill();

            let stdout = background_stdout_future
                .await
                .expect("could not read stdout");
            let stderr = background_stderr_future
                .await
                .expect("could not read stderr");

            let logs = format_logs(&stdout, &stderr);

            eprintln!("[{}; {}]: {} ⊢ (waiting)", time_of_day, run_status, context);
            let background_status = running_background.result().await;
            eprintln!(
                "[{}; {}]: {} ⊢ (finished) {}",
                time_of_day, run_status, context, background_status.value
            );

            if (background_status.value == StatusResultValue::Error
                || foreground_result.values.contains(&StatusResultValue::Error)
                || context.opt.logs)
                && !logs.is_empty()
            {
                eprintln!("{} {}", context, "╔════════════════════════".blue());
                for line in logs.lines() {
                    eprintln!("{} {} {}", context, "║".blue(), line);
                }
                eprintln!("{} {}", context, "╚════════════════════════".blue());
            }

            step_result.values = foreground_result.values;
            step_result
                .failed_steps_prefixes
                .append(&mut foreground_result.failed_steps_prefixes);

            // Also propagate the status of the background process.
            if background_status.value == StatusResultValue::Error {
                step_result
                    .failed_steps_prefixes
                    .push(format!("{}", context));
            }
            step_result.values.insert(background_status.value);

            run_status.update(
                &context,
                step_result.values.contains(&StatusResultValue::Error),
            );
        }
    }
    step_result
}

/// A single command.
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
    fn description(&self) -> String {
        format!("{} {}", self.executable, self.args.join(" "))
    }
    /// Run the provided command, printing a status message with the current prefix.
    /// TODO(#396): Return one of three results: pass, fail, or internal error (e.g. if the binary
    /// to run was not found).
    fn run(self: Box<Self>, opt: &Opt) -> Box<dyn Running> {
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

        if opt.dry_run {
            Box::new(SingleStatusResult {
                value: StatusResultValue::Skipped,
                logs: String::new(),
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
            let child = cmd
                // Close stdin to avoid hanging.
                .stdin(std::process::Stdio::null())
                .stdout(stdout)
                .stderr(stderr)
                .spawn()
                .unwrap_or_else(|err| panic!("could not spawn command: {:?}: {}", cmd, err));

            crate::PROCESSES
                .lock()
                .expect("could not acquire processes lock")
                .push(child.id() as i32);

            Box::new(RunningCmd { child })
        }
    }
}

pub fn kill_process(pid: i32) {
    // TODO(#396): Send increasingly stronger signals if the process fails to terminate
    // within a given amount of time.
    let pid = nix::unistd::Pid::from_raw(pid);
    // Ignore errors.
    let _ = nix::sys::signal::kill(pid, nix::sys::signal::Signal::SIGINT);
}

struct RunningCmd {
    child: tokio::process::Child,
}

#[async_trait]
impl Running for RunningCmd {
    fn kill(&mut self) {
        kill_process(self.child.id() as i32);
    }

    fn stdout(&mut self) -> Box<dyn AsyncRead + Send + Unpin> {
        match self.child.stdout.take() {
            Some(stdout) => Box::new(stdout),
            None => Box::new(empty()),
        }
    }
    fn stderr(&mut self) -> Box<dyn AsyncRead + Send + Unpin> {
        match self.child.stderr.take() {
            Some(stderr) => Box::new(stderr),
            None => Box::new(empty()),
        }
    }

    async fn result(mut self: Box<Self>) -> SingleStatusResult {
        let output = self
            .child
            .wait_with_output()
            .await
            .expect("could not get exit status");
        let logs = format_logs(&output.stdout, &output.stderr);
        if output.status.success() {
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
}

fn format_logs(stdout: &[u8], stderr: &[u8]) -> String {
    let mut logs = String::new();
    if !stdout.is_empty() {
        logs += &format!(
            "════╡ stdout ╞════\n{}",
            std::str::from_utf8(stdout).expect("could not parse stdout as UTF8")
        );
    }
    if !stderr.is_empty() {
        logs += &format!(
            "════╡ stderr ╞════\n{}",
            std::str::from_utf8(stderr).expect("could not parse stderr as UTF8")
        );
    }
    logs
}

/// A task that can be run asynchronously.
pub trait Runnable: Send {
    /// Returns a description of the task, e.g. the command line arguments that are part of it.
    fn description(&self) -> String;
    /// Starts the task and returns a [`Running`] implementation.
    fn run(self: Box<Self>, opt: &Opt) -> Box<dyn Running>;
}

/// A task that is currently running asynchronously.
#[async_trait]
pub trait Running: Send {
    /// Attempts to kill the running task.
    fn kill(&mut self) {}
    /// Returns an [`AsyncRead`] object to stream stdout logs from the task.
    fn stdout(&mut self) -> Box<dyn AsyncRead + Send + Unpin> {
        Box::new(empty())
    }
    /// Returns an [`AsyncRead`] object to stream stderr logs from the task.
    fn stderr(&mut self) -> Box<dyn AsyncRead + Send + Unpin> {
        Box::new(empty())
    }
    /// Returns the final result of the task, upon spontaneous termination.
    async fn result(self: Box<Self>) -> SingleStatusResult;
}

#[async_trait]
impl Running for SingleStatusResult {
    async fn result(self: Box<Self>) -> SingleStatusResult {
        *self
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
