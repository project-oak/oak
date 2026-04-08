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

//! End-to-end integration tests for the `crate_vendor` binary.
//!
//! These tests run the actual binary via `cleanroom run` against a
//! checked-in `Cargo.lock` file and verify the output structure,
//! checksums, and generated config.
//!
//! Run via:
//! ```text
//! bazel test //cleanroom/examples/crate_vendor:crate_vendor_integration_test
//! ```

use std::{
    env, fs,
    io::Write,
    path::PathBuf,
    process::{Command, Stdio},
};

/// Resolves a Bazel runfile path from the environment variable `var`.
fn env_path(var: &str) -> PathBuf {
    PathBuf::from(env::var(var).expect("env var not set"))
}

/// Runs crate_vendor through `cleanroom run` with the given JSON config
/// as stdin. Returns `(stdout, stderr, success)`.
fn run_crate_vendor(
    config_json: &str,
    mappings: &[(&std::path::Path, &str)],
) -> (String, String, bool) {
    let bin = env_path("CLEANROOM_BIN");
    let wasm = env_path("CRATE_VENDOR_WASM");

    let mut child = Command::new(&bin)
        .arg("run-local")
        .arg(&wasm)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn cleanroom");

    child.stdin.take().unwrap().write_all(config_json.as_bytes()).expect("writing stdin");

    let output = child.wait_with_output().expect("waiting for cleanroom");

    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        output.status.success(),
    )
}

/// The number of registry (crates.io) packages in testdata/Cargo.lock.
/// oak_time itself is not a registry package, so it's excluded.
const EXPECTED_CRATE_COUNT: usize = 21;

/// A few crates we expect to find, with their checksums from the lockfile.
const EXPECTED_CRATES: &[(&str, &str)] = &[
    ("anyhow-1.0.98", "e16d2d3311acee920a9eb8d33b8cbc1787ce4a264e85f964c2404b969bdcd487"),
    ("memchr-2.7.5", "32a282da65faaf38286cf3be983213fcf1d2e2a58700e808f83f4ea9a4804bc0"),
    ("unicode-ident-1.0.18", "5a5f39404a5da50712a4c1eecf25e90dd62b613502b7e925fd4e4d19b5c96512"),
];

// -----------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------

#[test]
fn dry_run_lists_all_crates() {
    let lockfile = env_path("TEST_CARGO_LOCK");
    let config = serde_json::json!({
        "lockfile": lockfile.to_str().unwrap(),
        "dry_run": true,
    });

    let (stdout, stderr, ok) = run_crate_vendor(&config.to_string(), &[]);

    assert!(ok, "crate_vendor --dry-run should succeed. stderr: {stderr}");

    // Should list all 21 registry crates.
    assert!(
        stdout.contains(&format!("{EXPECTED_CRATE_COUNT} crates would be downloaded")),
        "expected {EXPECTED_CRATE_COUNT} crates in dry-run output, got:\n{stdout}",
    );

    // Spot-check a few crate names.
    for (name, _checksum) in EXPECTED_CRATES {
        assert!(stdout.contains(name), "dry-run output should mention {name}",);
    }
}

#[test]
fn vendor_downloads_and_extracts_crates() {
    let lockfile = env_path("TEST_CARGO_LOCK");
    let tmp = tempfile::tempdir().expect("failed to create tempdir");
    let vendor_dir = tmp.path().join("vendor");
    fs::create_dir_all(&vendor_dir).unwrap();

    let config = serde_json::json!({
        "lockfile": lockfile.to_str().unwrap(),
        "output_dir": vendor_dir.to_str().unwrap(),
    });

    let (stdout, stderr, ok) = run_crate_vendor(&config.to_string(), &[]);

    assert!(ok, "crate_vendor should succeed. stderr: {stderr}");
    assert!(
        stdout.contains(&format!("{EXPECTED_CRATE_COUNT} downloaded")),
        "expected {EXPECTED_CRATE_COUNT} downloads, got:\n{stdout}",
    );

    // Verify the right number of directories were created.
    let entries: Vec<_> = fs::read_dir(&vendor_dir)
        .expect("vendor dir should exist")
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().map(|t| t.is_dir()).unwrap_or(false))
        .collect();
    assert_eq!(
        entries.len(),
        EXPECTED_CRATE_COUNT,
        "expected {EXPECTED_CRATE_COUNT} vendored crate dirs, found {}",
        entries.len(),
    );

    // Verify specific crates have the right structure.
    for (name, checksum) in EXPECTED_CRATES {
        let crate_dir = vendor_dir.join(name);
        assert!(crate_dir.is_dir(), "{name} directory should exist");

        // Must contain a Cargo.toml.
        assert!(crate_dir.join("Cargo.toml").is_file(), "{name}/Cargo.toml should exist",);

        // Must contain .cargo-checksum.json with the correct package hash.
        let checksum_path = crate_dir.join(".cargo-checksum.json");
        assert!(checksum_path.is_file(), "{name}/.cargo-checksum.json should exist",);
        let checksum_content =
            fs::read_to_string(&checksum_path).expect("failed to read checksum file");
        let checksum_json: serde_json::Value =
            serde_json::from_str(&checksum_content).expect("checksum file should be valid JSON");
        assert_eq!(
            checksum_json["package"].as_str().unwrap(),
            *checksum,
            "{name} checksum mismatch",
        );
    }
}

#[test]
fn vendor_is_idempotent() {
    let lockfile = env_path("TEST_CARGO_LOCK");
    let tmp = tempfile::tempdir().expect("failed to create tempdir");
    let vendor_dir = tmp.path().join("vendor");
    fs::create_dir_all(&vendor_dir).unwrap();

    let config = serde_json::json!({
        "lockfile": lockfile.to_str().unwrap(),
        "output_dir": vendor_dir.to_str().unwrap(),
    });

    // First run: all downloads.
    let (_stdout, stderr, ok) = run_crate_vendor(&config.to_string(), &[]);
    assert!(ok, "first run should succeed. stderr: {stderr}");

    // Second run: everything should be skipped.
    let (stdout, stderr, ok) = run_crate_vendor(&config.to_string(), &[]);
    assert!(ok, "second run should succeed. stderr: {stderr}");
    assert!(stdout.contains("0 downloaded"), "second run should download nothing, got:\n{stdout}",);
    assert!(
        stdout.contains(&format!("{EXPECTED_CRATE_COUNT} already present")),
        "second run should report all as already present, got:\n{stdout}",
    );
}

#[test]
fn config_toml_is_generated() {
    let lockfile = env_path("TEST_CARGO_LOCK");
    let tmp = tempfile::tempdir().expect("failed to create tempdir");
    let vendor_dir = tmp.path().join("vendor");
    let config_dir = tmp.path().join(".cargo");
    fs::create_dir_all(&vendor_dir).unwrap();
    fs::create_dir_all(&config_dir).unwrap();

    let config = serde_json::json!({
        "lockfile": lockfile.to_str().unwrap(),
        "output_dir": vendor_dir.to_str().unwrap(),
        "config_dir": config_dir.to_str().unwrap(),
    });

    let (_stdout, stderr, ok) = run_crate_vendor(&config.to_string(), &[]);

    assert!(ok, "crate_vendor should succeed. stderr: {stderr}");

    let config_path = config_dir.join("config.toml");
    assert!(config_path.is_file(), "config.toml should be generated");

    let config = fs::read_to_string(&config_path).expect("failed to read config.toml");
    assert!(config.contains("[source.crates-io]"), "config should contain [source.crates-io]",);
    assert!(
        config.contains("replace-with = \"vendored-sources\""),
        "config should redirect crates-io to vendored-sources",
    );
    assert!(
        config.contains("[source.vendored-sources]"),
        "config should contain [source.vendored-sources]",
    );
}
