// Copyright 2025 The Project Oak Authors
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

//! Integration tests for the `falsify_wasm` runner.
//!
//! These tests build example claims as Wasm modules, run them through the
//! `falsify_wasm` CLI, and verify the TOML output.
//!
//! Paths to the binary and Wasm modules are injected via environment variables
//! set by Bazel's `env` + `$(location)` macros in the BUILD file.

use std::{env, fs, process::Command};

fn env_path(var: &str) -> String {
    let relative =
        env::var(var).unwrap_or_else(|_| panic!("{var} env var not set — run via `bazel test`"));
    let runfiles = env::var("RUNFILES_DIR").expect("RUNFILES_DIR not set");
    format!("{runfiles}/_main/{relative}")
}

/// Runs the falsify_wasm CLI with the given Wasm module and input bytes.
/// Returns the TOML output string.
fn run_falsify_wasm(wasm_module: &str, input_bytes: &[u8]) -> String {
    let tmp = tempfile::tempdir().expect("failed to create tmpdir");
    let input_path = tmp.path().join("input.bin");
    let output_path = tmp.path().join("output.toml");

    fs::write(&input_path, input_bytes).expect("failed to write input file");

    let bin = env_path("FALSIFY_WASM_BIN");
    let status = Command::new(&bin)
        .arg(format!("--wasm-module={wasm_module}"))
        .arg(format!("--input-file={}", input_path.display()))
        .arg(format!("--output-file-toml={}", output_path.display()))
        .status()
        .expect("failed to execute falsify_wasm");

    assert!(status.success(), "falsify_wasm exited with: {status}");

    fs::read_to_string(&output_path).expect("failed to read output TOML")
}

#[test]
fn intact_when_no_repeated_bytes() {
    let toml = run_falsify_wasm(&env_path("NO_REPEATED_BYTES_WASM"), b"abcd");
    assert!(toml.contains("Intact"), "Expected Intact in TOML output, got:\n{toml}");
}

#[test]
fn falsified_when_repeated_bytes() {
    let toml = run_falsify_wasm(&env_path("NO_REPEATED_BYTES_WASM"), b"aab");
    assert!(toml.contains("Falsified"), "Expected Falsified in TOML output, got:\n{toml}");
}

#[test]
fn intact_for_empty_input() {
    let toml = run_falsify_wasm(&env_path("NO_REPEATED_BYTES_WASM"), b"");
    assert!(toml.contains("Intact"), "Expected Intact in TOML output, got:\n{toml}");
}

#[test]
fn intact_for_single_byte() {
    let toml = run_falsify_wasm(&env_path("NO_REPEATED_BYTES_WASM"), b"x");
    assert!(toml.contains("Intact"), "Expected Intact in TOML output, got:\n{toml}");
}

#[test]
fn claim_error_when_module_panics() {
    let toml = run_falsify_wasm(&env_path("ALWAYS_PANICS_WASM"), b"anything");
    assert!(toml.contains("ClaimError"), "Expected ClaimError in TOML output, got:\n{toml}");
}
