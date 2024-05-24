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

use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
    time::Instant,
};

use async_recursion::async_recursion;
use async_trait::async_trait;
use clap::{Parser, Subcommand};
use colored::*;
use nix::sys::signal::Signal;
use strum_macros::EnumIter;
use tokio::io::{empty, AsyncRead, AsyncReadExt};

use crate::PROCESSES;

#[derive(Parser, Clone)]
pub struct Opt {
    #[arg(long, help = "do not execute commands")]
    pub dry_run: bool,
    #[arg(long, help = "show logs of commands")]
    pub logs: bool,
    #[arg(long, help = "continue execution after error")]
    pub keep_going: bool,
    #[command(subcommand)]
    pub cmd: Command,
}

#[derive(Subcommand, Clone, Debug)]
pub enum Command {
    Format,
    CheckFormat,
    RunTests,
    RunCargoClippy,
    RunCargoFuzz(RunCargoFuzz),
    RunCargoDeny,
    RunCargoUdeps,
    #[command(about = "generate bash completion script to stdout")]
    Completion(Completion),
}

#[derive(Parser, Clone, Debug)]
pub struct Completion {
    #[arg(
        long,
        help = "file name to write xtask_bash_completion with full path; defaults to .xtask_bash_completion in current directory",
        default_value = ".xtask_bash_completion"
    )]
    pub file_name: PathBuf,
}

/// Holds the options for running the example.
#[derive(Parser, Clone, Debug)]
pub struct RunOakExampleOpt {
    #[arg(
        long,
        help = "name of a single example to run (i.e. the Rust crate name of the Wasm module)"
    )]
    pub example_name: String,
    #[arg(long, help = "path to the lookup data file")]
    pub lookup_data_path: Option<String>,
}

#[derive(Parser, Clone, Debug)]
pub struct BuildClient {
    #[arg(
        long,
        help = "client variant: [all, rust, cpp, go, nodejs, none] [default: all]",
        default_value = "all"
    )]
    pub client_variant: String,
    #[arg(
        long,
        help = "rust toolchain override to use for the client compilation [e.g. stable, nightly, stage2]"
    )]
    pub client_rust_toolchain: Option<String>,
    #[arg(
        long,
        help = "rust target to use for the client compilation [e.g. x86_64-unknown-linux-gnu, x86_64-unknown-linux-musl, x86_64-apple-darwin]"
    )]
    pub client_rust_target: Option<String>,
}

#[derive(serde::Deserialize, Default, Debug, Clone, PartialEq, EnumIter)]
pub enum ServerVariant {
    /// Production-like server variant, without logging or any of the
    /// experimental features enabled
    #[default]
    Base,
}

impl std::str::FromStr for ServerVariant {
    type Err = String;
    fn from_str(variant: &str) -> Result<Self, Self::Err> {
        match variant {
            "base" => Ok(ServerVariant::Base),
            _ => Err(format!("couldn't parse functions server variant {}", variant)),
        }
    }
}

impl ServerVariant {
    // Get path to manifest for the variant.
    pub fn path_to_manifest(&self) -> &'static str {
        match self {
            ServerVariant::Base => "./oak_functions_launcher",
        }
    }

    /// Get path to the executable server binary for the server variant.
    pub fn path_to_executable(&self) -> &'static str {
        match self {
            ServerVariant::Base => {
                "./target/x86_64-unknown-linux-musl/release/oak_functions_launcher"
            }
        }
    }
}

#[derive(Parser, Clone, Debug)]
pub struct RunTestsOpt {
    #[arg(long, help = "Remove generated files after running tests for each crate")]
    pub cleanup: bool,
}

#[derive(Parser, Clone, Debug)]
pub struct RunCargoFuzz {
    #[arg(long, help = "name of a specific fuzz-target. If not specified, runs all fuzz targets.")]
    pub target_name: Option<String>,
    /// Additional `libFuzzer` arguments passed through to the binary
    #[arg(last(true))]
    pub args: Vec<String>,
}

/// Partial representation of Cargo manifest files.
///
/// Only the fields that are required for extracting specific information (e.g.,
/// names of fuzz targets) are included.
#[derive(serde::Deserialize, Debug)]
pub struct CargoManifest {
    #[serde(default)]
    pub bin: Vec<CargoBinary>,
    #[serde(default)]
    pub dependencies: HashMap<String, Dependency>,
    #[serde(default)]
    #[serde(rename = "dev-dependencies")]
    pub dev_dependencies: HashMap<String, Dependency>,
    #[serde(default)]
    #[serde(rename = "build-dependencies")]
    pub build_dependencies: HashMap<String, Dependency>,
}

/// Partial information about a Cargo binary, as included in a Cargo manifest.
#[derive(serde::Deserialize, Debug)]
pub struct CargoBinary {
    #[serde(default)]
    pub name: String,
}

/// Partial representation of a dependency in a `Cargo.toml` file.
#[derive(serde::Deserialize, Debug, PartialEq, PartialOrd)]
#[serde(untagged)]
pub enum Dependency {
    /// Plaintext specification of a dependency with only the version number.
    Text(String),
    /// Json specification of a dependency.
    Json(DependencySpec),
}

/// Partial representation of a Json specification of a dependency in a
/// `Cargo.toml` file.
#[derive(serde::Deserialize, Debug, PartialEq, PartialOrd)]
pub struct DependencySpec {
    #[serde(default)]
    pub path: Option<String>,
}

impl CargoManifest {
    pub fn all_dependencies_with_toml_path(self) -> Vec<String> {
        let all_deps = vec![
            self.dependencies.into_values().collect(),
            self.dev_dependencies.into_values().collect(),
            self.build_dependencies.into_values().collect(),
        ];
        let all_deps: Vec<Dependency> = itertools::concat(all_deps);

        // Collect all the dependencies that specify a path.
        all_deps
            .iter()
            .map(|dep| match dep {
                Dependency::Json(spec) => spec.path.clone(),
                Dependency::Text(_) => None,
            })
            .filter(|path| path.is_some())
            .map(|path| {
                let mut path = PathBuf::from(path.unwrap());
                path.push("Cargo.toml");
                path.to_str().unwrap().to_string()
            })
            .collect()
    }
}

/// Struct representing config files for fuzzing.
#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct FuzzConfig {
    pub examples: Vec<FuzzableExample>,
}

/// Config for building an example for fuzzing.
#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct FuzzableExample {
    /// Name of the example
    pub name: String,
    /// Path to the Cargo.toml file for the example.
    pub manifest_path: String,
    /// Path to desired location of the .wasm file.
    pub out_dir: String,
}

/// A construct to keep track of the status of the execution. It only cares
/// about the top-level steps.
#[derive(Clone)]
pub struct Status {
    error: usize,
    ok: usize,
    remaining: usize,
}

impl Status {
    pub fn new(remaining: usize) -> Self {
        Status { error: 0, ok: 0, remaining }
    }

    /// Guarantees that the `error`, `ok`, and `remaining` counts are updated
    /// only after the completions of each top-level step.
    fn update(&mut self, context: &Context, step_has_error: bool) {
        // Update the status with results from the step, only if it is a top-level step.
        if context.depth() == 1 {
            self.remaining -= 1;
            // We only care about pass (`ok`) and fail (`error`). If an entire step is
            // skipped, we count it as a passed step.
            if step_has_error {
                self.error += 1;
            } else {
                self.ok += 1;
            }
        }
    }
}

/// Formats the status as `E:<error-count>,O:<ok-count>,R:<remaining-count>`,
/// suitable for annotating the log lines.
impl std::fmt::Display for Status {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "✓:{},✗:{},⠇:{}", self.ok, self.error, self.remaining)
    }
}

/// Encapsulates all the local state relative to a step, and is propagated to
/// child steps.
pub struct Context {
    opt: Opt,
    prefix: Vec<String>,
}

impl Context {
    pub fn root(opt: &Opt) -> Self {
        Context { opt: opt.clone(), prefix: vec![] }
    }

    fn child(&self, name: &str) -> Self {
        let mut prefix = self.prefix.clone();
        prefix.push(name.to_string());
        Context { opt: self.opt.clone(), prefix }
    }

    fn depth(&self) -> usize {
        self.prefix.len()
    }

    fn header(&self) -> String {
        let margin = "│".repeat(self.depth() - 1);
        format!("{}┌[{}]", margin, self.prefix.last().unwrap().cyan())
    }

    /// Prints a footer that repeats information from the header.
    ///
    /// Useful when footer and header are expected to be far away from each
    /// other.
    fn footer_long(&self) -> String {
        let margin = "│".repeat(self.depth() - 1);
        format!("{}└[{}]─▶", margin, self.prefix.last().unwrap().cyan())
    }

    /// Prints a footer that does not repeat information from the header.
    ///
    /// Useful when it follows the header almost immediately.
    fn footer_short(&self) -> String {
        let margin = "│".repeat(self.depth() - 1);
        format!("{}└─▶", margin)
    }

    fn margin(&self) -> String {
        "│".repeat(self.depth())
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

/// An execution step, which may be a single `Runnable`, or a collection of
/// sub-steps.
pub enum Step {
    Single { name: String, command: Box<dyn Runnable> },
    Multiple { name: String, steps: Vec<Step> },
}

impl Step {
    /// Returns the number of top-level steps or commands. The number of
    /// sub-steps is not recursively accumulated in the returned length.
    pub fn len(&self) -> usize {
        match self {
            Step::Single { name: _, command: _ } => 1,
            Step::Multiple { name: _, steps: s } => s.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Default)]
pub struct StepResult {
    pub values: HashSet<StatusResultValue>,
    pub failed_steps_prefixes: Vec<String>,
}

impl StepResult {
    pub fn success(&self) -> bool {
        self.values.len() == 1 && self.values.contains(&StatusResultValue::Ok)
    }
}

fn values_to_string<T>(values: T) -> String
where
    T: IntoIterator,
    T::Item: std::fmt::Display,
{
    format!("[{}]", values.into_iter().map(|v| v.to_string()).collect::<Vec<_>>().join(","))
}

/// Reads the entire content of the provided future into a vector.
pub async fn read_to_end<A: AsyncRead + Unpin>(mut io: A) -> Vec<u8> {
    let mut buf = Vec::new();
    io.read_to_end(&mut buf).await.expect("couldn't read from future");
    buf
}

/// Run the provided step, printing out information about the execution, and
/// returning a set of status results from the single or multiple steps that
/// were executed.
#[async_recursion]
pub async fn run_step(context: &Context, step: Step, mut run_status: Status) -> StepResult {
    let mut step_result = StepResult::default();
    fn prefix(run_status: &Status) -> String {
        let now = chrono::Utc::now();
        let time_of_day = now.format("%H:%M:%S");
        format!("[{} {}] ", time_of_day, run_status)
    }
    match step {
        Step::Single { name, command } => {
            let context = context.child(&name);

            let start = Instant::now();

            eprintln!("{}{}", prefix(&run_status), context.header());

            eprintln!(
                "{}{} {}",
                prefix(&run_status),
                context.margin(),
                command.description().blue()
            );

            let status = command.run(&context.opt).result().await;
            let end = Instant::now();
            let elapsed = end.duration_since(start);

            let step_failed = status.value == StatusResultValue::Error;
            if (step_failed || context.opt.logs) && !status.logs.is_empty() {
                eprintln!(
                    "{}{} {}",
                    prefix(&run_status),
                    context.margin(),
                    "╔════════════════════════".blue()
                );
                for line in status.logs.lines() {
                    eprintln!(
                        "{}{} {} {}",
                        prefix(&run_status),
                        context.margin(),
                        "║".blue(),
                        line
                    );
                }
                eprintln!(
                    "{}{} {}",
                    prefix(&run_status),
                    context.margin(),
                    "╚════════════════════════".blue()
                );
                step_result.failed_steps_prefixes.push(format!("{}", context));
            }

            eprintln!(
                "{}{}{} {:.0?}",
                prefix(&run_status),
                context.footer_short(),
                status.value,
                elapsed
            );

            step_result.values.insert(status.value);
            run_status.update(&context, step_failed);
        }
        Step::Multiple { name, steps } => {
            let context = context.child(&name);
            eprintln!("{}{}", prefix(&run_status), context.header());
            let start = Instant::now();
            for step in steps {
                let mut result = run_step(&context, step, run_status.clone()).await;
                step_result.values = step_result.values.union(&result.values).cloned().collect();
                step_result.failed_steps_prefixes.append(&mut result.failed_steps_prefixes);
                let failed = result.values.contains(&StatusResultValue::Error);
                run_status.update(&context, failed);
                if failed && !context.opt.keep_going {
                    break;
                }
            }
            let end = Instant::now();
            let elapsed = end.duration_since(start);
            eprintln!(
                "{}{}{} {:.0?}",
                prefix(&run_status),
                context.footer_long(),
                values_to_string(&step_result.values),
                elapsed
            );
        }
    }
    step_result
}

/// A single command.
pub struct Cmd {
    executable: String,
    args: Vec<String>,
    current_dir: Option<PathBuf>,
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
            current_dir: None,
        })
    }

    pub fn new_in_dir<I, S>(executable: &str, args: I, current_dir: &Path) -> Box<Self>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        Box::new(Cmd {
            executable: executable.to_string(),
            args: args.into_iter().map(|s| s.as_ref().to_string()).collect(),
            current_dir: Some(current_dir.to_path_buf()),
        })
    }
}

impl Runnable for Cmd {
    fn description(&self) -> String {
        format!(
            "{} {}{}",
            self.executable,
            self.args.join(" "),
            self.current_dir
                .as_ref()
                .map_or("".to_string(), |dir| format!(" (in directory {})", dir.display()))
        )
    }
    /// Run the provided command, printing a status message with the current
    /// prefix. TODO(#396): Return one of three results: pass, fail, or
    /// internal error (e.g. if the binary to run was not found).
    fn run(self: Box<Self>, opt: &Opt) -> Box<dyn Running> {
        let mut cmd = tokio::process::Command::new(&self.executable);
        cmd.args(&self.args);

        // Ensure that the child process is killed when the `Running` instance is
        // dropped (including on panic).
        cmd.kill_on_drop(true);

        if opt.dry_run {
            Box::new(SingleStatusResult { value: StatusResultValue::Skipped, logs: String::new() })
        } else {
            // If the `logs` flag is enabled, inherit stdout and stderr from the main xtask
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
            if let Some(current_dir) = self.current_dir {
                cmd.current_dir(current_dir);
            }

            let child = cmd
                // Close stdin to avoid hanging.
                .stdin(std::process::Stdio::null())
                .stdout(stdout)
                .stderr(stderr)
                .spawn()
                .unwrap_or_else(|err| panic!("couldn't spawn command: {:?}: {}", cmd, err));

            if let Some(pid) = child.id() {
                PROCESSES.lock().expect("couldn't acquire processes lock").push(pid as i32);
            }

            Box::new(RunningCmd { child })
        }
    }
}

pub fn process_gone(raw_pid: i32) -> bool {
    // Shell out to `ps` as there's no portable Rust equivalent.
    let mut cmd = std::process::Command::new("ps");
    cmd.args(["-p", &format!("{}", raw_pid)]);
    let mut child = cmd
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .unwrap_or_else(|err| panic!("couldn't spawn command: {:?}: {}", cmd, err));
    let output = child.wait().expect("couldn't get exit status");
    // ps -p has success exit code if the pid exists.
    !output.success()
}

pub fn kill_process(raw_pid: i32) {
    let pid = nix::unistd::Pid::from_raw(raw_pid);
    for i in 0..5 {
        if process_gone(raw_pid) {
            return;
        }

        // Ignore errors.
        let _ = nix::sys::signal::kill(pid, Signal::SIGINT);

        std::thread::sleep(std::time::Duration::from_millis(200 * i));
    }
    let _ = nix::sys::signal::kill(pid, Signal::SIGKILL);
}

struct RunningCmd {
    child: tokio::process::Child,
}

#[async_trait]
impl Running for RunningCmd {
    fn kill(&mut self) {
        if let Some(pid) = self.child.id() {
            kill_process(pid as i32);
        }
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
        let output = self.child.wait_with_output().await.expect("couldn't get exit status");
        let logs = format_logs(&output.stdout, &output.stderr);
        if output.status.success() {
            SingleStatusResult { value: StatusResultValue::Ok, logs }
        } else {
            SingleStatusResult { value: StatusResultValue::Error, logs }
        }
    }
}

fn format_logs(stdout: &[u8], stderr: &[u8]) -> String {
    let mut logs = String::new();
    if !stdout.is_empty() {
        logs += &format!(
            "════╡ stdout ╞════\n{}",
            std::str::from_utf8(stdout).expect("couldn't parse stdout as UTF8")
        );
    }
    if !stderr.is_empty() {
        logs += &format!(
            "════╡ stderr ╞════\n{}",
            std::str::from_utf8(stderr).expect("couldn't parse stderr as UTF8")
        );
    }
    logs
}

/// A task that can be run asynchronously.
pub trait Runnable: Send {
    /// Returns a description of the task, e.g. the command line arguments that
    /// are part of it.
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

/// Similar to the `vec!` macro, but also allows a "spread" operator syntax
/// (`...`) to inline and expand nested iterable values.
///
/// See <https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Spread_syntax>.
#[macro_export]
macro_rules! spread [
    // Empty case.
    () => (
        [].iter()
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
        [$v].iter()
    );
    // Single value recursive case.
    ($v:expr, $($rest:tt)*) => (
        [$v].iter().chain( spread![$($rest)*] )
    );
];

#[test]
fn test_spread() {
    assert_eq!(vec![1], spread![1].cloned().collect::<Vec<i32>>());
    assert_eq!(vec![1, 2], spread![1, 2].cloned().collect::<Vec<i32>>());
    assert_eq!(vec![1, 2, 3, 4], spread![1, 2, 3, 4].cloned().collect::<Vec<i32>>());
    assert_eq!(vec![1, 2, 3, 4], spread![...[1, 2], 3, 4].cloned().collect::<Vec<i32>>());
    assert_eq!(vec![1, 2, 3, 4], spread![1, ...[2, 3], 4].cloned().collect::<Vec<i32>>());
    assert_eq!(vec![1, 2, 3, 4], spread![1, 2, ...[3, 4]].cloned().collect::<Vec<i32>>());
    assert_eq!(vec![1, 2, 3, 4], spread![...[1, 2], ...[3, 4]].cloned().collect::<Vec<i32>>());
    assert_eq!(vec![1, 2, 3, 4], spread![...[1, 2, 3, 4]].cloned().collect::<Vec<i32>>());

    assert_eq!(vec!["foo", "bar"], spread!["foo", "bar"].cloned().collect::<Vec<_>>());
}
