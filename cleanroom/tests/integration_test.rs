// Copyright 2026 The Project Oak Authors
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

//! Integration tests for the `cleanroom` runner.
//!
//! Each test builds an example Wasm module with Bazel (via `data` + `env`
//! attributes in the BUILD), runs the `cleanroom` binary with that module,
//! and verifies the output.
//!
//! Run via:
//! ```text
//! bazel test //cleanroom:cleanroom_integration_test
//! ```

use std::{
    env,
    io::Write,
    process::{Command, Stdio},
};

/// Resolves a Bazel runfile path from the environment variable `var`.
fn env_path(var: &str) -> String {
    let relative =
        env::var(var).unwrap_or_else(|_| panic!("{var} env var not set — run via `bazel test`"));
    let runfiles = env::var("RUNFILES_DIR").expect("RUNFILES_DIR not set");
    format!("{runfiles}/_main/{relative}")
}

/// Runs the cleanroom binary with the given Wasm module and stdin bytes.
/// Returns `(stdout_bytes, stderr_string, exit_status_success)`.
fn run_cleanroom(wasm_module: &str, stdin_bytes: &[u8]) -> (Vec<u8>, String, bool) {
    let bin = env_path("CLEANROOM_BIN");

    let mut child = Command::new(&bin)
        .arg(format!("--wasm-module-file={wasm_module}"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn cleanroom");

    child.stdin.take().unwrap().write_all(stdin_bytes).expect("failed to write stdin");

    let output = child.wait_with_output().expect("failed to wait for cleanroom");

    (output.stdout, String::from_utf8_lossy(&output.stderr).into_owned(), output.status.success())
}

// --- to_uppercase ---

#[test]
fn to_uppercase_basic() {
    let wasm = env_path("TO_UPPERCASE_WASM");
    let (out, _err, ok) = run_cleanroom(&wasm, b"hello world\n");
    assert!(ok, "cleanroom exited with failure");
    assert_eq!(out, b"HELLO WORLD\n");
}

#[test]
fn to_uppercase_empty_input() {
    let wasm = env_path("TO_UPPERCASE_WASM");
    let (out, _err, ok) = run_cleanroom(&wasm, b"");
    assert!(ok, "cleanroom exited with failure");
    assert_eq!(out, b"");
}

#[test]
fn to_uppercase_mixed_case() {
    let wasm = env_path("TO_UPPERCASE_WASM");
    let (out, _err, ok) = run_cleanroom(&wasm, b"Hello World 123!");
    assert!(ok, "cleanroom exited with failure");
    assert_eq!(out, b"HELLO WORLD 123!");
}

// --- reverse ---

#[test]
fn reverse_basic() {
    let wasm = env_path("REVERSE_WASM");
    let (out, _err, ok) = run_cleanroom(&wasm, b"hello");
    assert!(ok, "cleanroom exited with failure");
    assert_eq!(out, b"olleh");
}

#[test]
fn reverse_empty() {
    let wasm = env_path("REVERSE_WASM");
    let (out, _err, ok) = run_cleanroom(&wasm, b"");
    assert!(ok, "cleanroom exited with failure");
    assert_eq!(out, b"");
}

#[test]
fn reverse_palindrome() {
    let wasm = env_path("REVERSE_WASM");
    let (out, _err, ok) = run_cleanroom(&wasm, b"racecar");
    assert!(ok, "cleanroom exited with failure");
    assert_eq!(out, b"racecar");
}

// --- word_count ---

#[test]
fn word_count_single_line() {
    let wasm = env_path("WORD_COUNT_WASM");
    // "hello world\n" = 1 line, 2 words, 12 bytes
    let (out, _err, ok) = run_cleanroom(&wasm, b"hello world\n");
    assert!(ok, "cleanroom exited with failure");
    assert_eq!(out, b"1 2 12\n");
}

#[test]
fn word_count_multi_line() {
    let wasm = env_path("WORD_COUNT_WASM");
    // "foo\nbar baz\n" = 2 lines, 3 words, 12 bytes
    let (out, _err, ok) = run_cleanroom(&wasm, b"foo\nbar baz\n");
    assert!(ok, "cleanroom exited with failure");
    assert_eq!(out, b"2 3 12\n");
}

#[test]
fn word_count_empty() {
    let wasm = env_path("WORD_COUNT_WASM");
    let (out, _err, ok) = run_cleanroom(&wasm, b"");
    assert!(ok, "cleanroom exited with failure");
    assert_eq!(out, b"0 0 0\n");
}
