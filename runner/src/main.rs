//! A utility binary to run tests and orchestrate examples and other tools within the repository,
//! for local development and CI.
//!
//! To invoke, run the following command from the root of the repository:
//!
//! ```
//! cargo run --manifest-path=./runner/Cargo.toml
//! ```

use colored::*;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// Return whether to ignore the specified path. This is used by the `walker` package to efficiently
/// avoid descending into blacklisted directories.
fn is_ignored_path(path: &PathBuf) -> bool {
    path.starts_with("./bazel-cache")
        || path.starts_with("./cargo-cache")
        || path.starts_with("./third_party")
        || path.starts_with("./.git")
        || path.ends_with("target") // Rust artifacts.
}

fn is_ignored_entry(entry: &walkdir::DirEntry) -> bool {
    let path = entry.clone().into_path();
    is_ignored_path(&path)
}

/// Return an iterator of all the first-party and non-ignored files in the repository, which can be
/// then additionally filtered by the caller.
fn source_files() -> impl Iterator<Item = PathBuf> {
    let walker = walkdir::WalkDir::new(".").into_iter();
    walker
        .filter_entry(|e| !is_ignored_entry(e))
        .filter_map(Result::ok)
        .map(|e| e.into_path())
}

/// Return whether the provided path refers to a Bazel file (`BUILD`, `WORKSPACE`, or `*.bzl`)
fn is_bazel_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename == "BUILD" || filename == "WORKSPACE" || filename.ends_with(".bzl")
}

/// Return whether the provided path refers to a markdown file (`*.md`)
fn is_markdown_file(path: &PathBuf) -> bool {
    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    filename.ends_with(".md")
}

fn main() {
    let step = Step::root();
    {
        let step = step.with_prefix("buildifier");
        for entry in source_files().filter(is_bazel_file) {
            step.with_prefix(entry.to_str().unwrap()).run_command(
                "buildifier",
                &["-lint=warn", "-mode=check", entry.to_str().unwrap()],
            );
        }
    }
    {
        let step = step.with_prefix("prettier");
        for entry in source_files().filter(is_markdown_file) {
            step.with_prefix(entry.to_str().unwrap())
                .run_command("prettier", &["--check", entry.to_str().unwrap()]);
        }
    }
    {
        let step = step.with_prefix("embedmd");
        for entry in source_files().filter(is_markdown_file) {
            step.with_prefix(entry.to_str().unwrap()).run_command(
                &format!("{}/bin/embedmd", std::env::var("GOPATH").unwrap()),
                &["-d", entry.to_str().unwrap()],
            );
        }
    }
    let cargo_manifests = ["./sdk/rust/Cargo.toml", "./examples/Cargo.toml"];
    {
        let step = step.with_prefix("cargo fmt");
        for m in cargo_manifests.iter() {
            let step = step.with_prefix(m);
            step.run_command(
                "cargo",
                &[
                    "fmt",
                    "--all",
                    &format!("--manifest-path={}", m),
                    "--",
                    "--check",
                ],
            );
        }
    }
    {
        let step = step.with_prefix("cargo test");
        for m in cargo_manifests.iter() {
            let step = step.with_prefix(m);
            step.run_command(
                "cargo",
                &["test", "--all-targets", &format!("--manifest-path={}", m)],
            );
        }
    }
    {
        let step = step.with_prefix("cargo test");
        for m in cargo_manifests.iter() {
            let step = step.with_prefix(m);
            step.run_command(
                "cargo",
                &[
                    "clippy",
                    "--all-targets",
                    &format!("--manifest-path={}", m),
                    "--",
                    "--deny=warnings",
                ],
            );
        }
    }
    {
        let step = step.with_prefix("bazel build");
        step.with_prefix("non-Asylo targets").run_command(
            "bazel",
            &["build", "--", "//oak/...:all", "-//oak/server/asylo:all"],
        );
    }
    {
        let step = step.with_prefix("bazel test");
        step.with_prefix("host targets").run_command(
            "bazel",
            // TODO: Extract these targets with `bazel query` at runtime, based on some label or
            // attribute.
            &[
                "test",
                "//oak/server:host_tests",
                "//oak/server/storage:host_tests",
                "//oak/common:host_tests",
            ],
        );
    }
}

/// A step executor, which pretty prints the current nesting level, and allows executing commands
/// and reporting their result.
struct Step {
    prefixes: Vec<String>,
}

impl Step {
    /// Create the root step executor, of which there should only be one.
    fn root() -> Self {
        Step {
            prefixes: Vec::new(),
        }
    }

    /// Create a child step executor, with the provided prefix.
    fn with_prefix(&self, prefix: &str) -> Step {
        let mut new_prefixes = self.prefixes.clone();
        new_prefixes.push(prefix.to_string());
        Step {
            prefixes: new_prefixes,
        }
    }

    /// Run the provided command, printing a status message with the current prefix.
    /// TODO: Add ability to run commands in parallel.
    /// TODO: Return one of three results: pass, fail, or internal error (e.g. if the binary to run
    /// was not found).
    fn run_command(&self, executable: &str, args: &[&str]) {
        // TODO: Measure and print elapsed time.
        // TODO: Add dry-run mode that only prints the commands but does not actually run them.
        eprint!("{} ⊢ ", self.prefixes.join(" ➡ "));
        std::io::stderr().flush().expect("could not flush stderr");
        let mut cmd = Command::new(executable);
        cmd.args(args);
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
            // TODO: Add `verbose` flag to always print logs.
            // TODO: Support both stdout and stderr.
            eprintln!(
                "⬇⬇⬇⬇\n{}\n⬆⬆⬆⬆",
                std::str::from_utf8(&output.stderr).expect("could not parse command output"),
            );
        }
    }
}
