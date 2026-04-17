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

//! End-to-end integration tests for the cleanroom system.
//!
//! These tests exercise the full pipeline:
//!
//! 1. **Direct mode** (`cleanroom run`): runs modules via the cleanroom binary
//!    with the Oak Functions ABI.
//! 2. **Server/client mode**: starts a cleanroom server on a Unix socket,
//!    communicates via the RPC protocol, and verifies IFC label tracking.
//!
//! # Running
//!
//! ```text
//! bazel test //cleanroom:cleanroom_integration_test
//! ```

use std::{
    env,
    io::Write,
    os::unix::net::UnixStream,
    path::PathBuf,
    process::{Command, Stdio},
};

/// Resolves a Bazel runfile path from the environment variable `var`.
fn env_path(var: &str) -> String {
    let relative =
        env::var(var).unwrap_or_else(|_| panic!("{var} env var not set — run via `bazel test`"));
    let runfiles = env::var("RUNFILES_DIR").expect("RUNFILES_DIR not set");
    format!("{runfiles}/_main/{relative}")
}

// ══════════════════════════════════════════════════════════════════
// Direct mode tests (`cleanroom run`)
// ══════════════════════════════════════════════════════════════════

/// Runs the cleanroom binary in direct mode with the given Wasm module
/// and stdin bytes.  Returns `(stdout_bytes, stderr_string, success)`.
fn run_cleanroom(wasm_module: &str, stdin_bytes: &[u8]) -> (Vec<u8>, String, bool) {
    let bin = env_path("CLEANROOM_BIN");

    let mut child = Command::new(&bin)
        .arg("run-local")
        .arg(wasm_module)
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
    let (out, err, ok) = run_cleanroom(&wasm, b"hello world\n");
    assert!(ok, "cleanroom exited with failure: {}", err);
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

// ══════════════════════════════════════════════════════════════════
// Server/client protocol tests
// ══════════════════════════════════════════════════════════════════
//
// These tests start a cleanroom server on a temporary Unix socket,
// install a test module in a temporary store, and exercise the RPC
// protocol.

/// Test harness that manages a cleanroom server process and module
/// store for integration testing.
#[allow(dead_code)]
struct ServerHarness {
    /// Temporary directory holding the module store.
    store_dir: tempfile::TempDir,
    /// Temporary directory holding the socket and policy file.
    socket_dir: tempfile::TempDir,
    /// The running server process.
    server_process: std::process::Child,
    /// Path to the Unix socket.
    socket_path: PathBuf,
}

impl ServerHarness {
    /// Creates a new server harness with the given policy and modules.
    ///
    /// `modules` is a list of `(name, wasm_env_var)` pairs where
    /// `wasm_env_var` is the Bazel env var pointing to the `.wasm`
    /// file.
    fn start(policy_toml: &str, cells_toml: &str, modules: &[(&str, &str)]) -> Self {
        let store_dir = tempfile::tempdir().expect("creating store dir");
        let socket_dir = tempfile::tempdir().expect("creating socket dir");

        // Create the sha256/ subdirectory in the store.
        std::fs::create_dir_all(store_dir.path().join("sha256")).expect("creating sha256 dir");

        // Install modules into the content-addressed store and build
        // the manifest.
        let mut manifest_lines = vec!["[modules]".to_string()];
        for (name, env_var) in modules {
            let wasm_path = env_path(env_var);
            let wasm_bytes =
                std::fs::read(&wasm_path).unwrap_or_else(|e| panic!("reading {wasm_path}: {e}"));

            // Compute SHA-256 digest.
            use sha2::{Digest, Sha256};
            let hash = Sha256::digest(&wasm_bytes);
            let hex_hash = hex::encode(hash);
            let digest = format!("sha256:{hex_hash}");

            // Copy to store.
            let dest = store_dir.path().join("sha256").join(&hex_hash);
            std::fs::write(&dest, &wasm_bytes).expect("writing module to store");

            manifest_lines.push(format!("{name} = \"{digest}\""));
        }

        // Write manifest.
        let manifest_path = store_dir.path().join("manifest.toml");
        std::fs::write(&manifest_path, manifest_lines.join("\n")).expect("writing manifest");

        // Write policy.
        let policy_path = socket_dir.path().join("policy.toml");
        std::fs::write(&policy_path, policy_toml).expect("writing policy");

        // Write cells if provided.
        let cells_path = socket_dir.path().join("cells.toml");
        std::fs::write(&cells_path, cells_toml).expect("writing cells");

        // Socket path.
        let socket_path = socket_dir.path().join("cleanroom.sock");

        // Start the server.
        let bin = env_path("CLEANROOM_BIN");
        let mut server_process = Command::new(&bin)
            .arg("server")
            .arg(format!("--policy-file={}", policy_path.display()))
            .arg(format!("--cells-file={}", cells_path.display()))
            .arg(format!("--socket={}", socket_path.display()))
            .arg(format!("--module-store={}", store_dir.path().display()))
            .env("RUST_LOG", "info")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .spawn()
            .expect("starting server");

        let mut socket_created = false;
        for _ in 0..50 {
            if socket_path.exists() {
                socket_created = true;
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(100));
        }

        if !socket_created {
            let mut server_err = String::new();
            use std::io::Read;
            if let Some(mut err) = server_process.stderr.take() {
                err.read_to_string(&mut server_err).unwrap();
            }
            panic!(
                "server did not create socket within 5 seconds.\nServer stderr:\n{}",
                server_err
            );
        }

        Self { store_dir, socket_dir, server_process, socket_path }
    }

    /// Connects to the server and sends a message from client to server,
    /// returning the message from server to client.
    fn send_request(
        &self,
        request: &cleanroom_protocol::ClientToServer,
    ) -> cleanroom_protocol::ServerToClient {
        let mut stream = UnixStream::connect(&self.socket_path).expect("connecting to server");
        cleanroom_protocol::write_message(&mut stream, request).expect("sending message");
        cleanroom_protocol::read_message(&mut stream).expect("reading response")
    }
}

impl Drop for ServerHarness {
    fn drop(&mut self) {
        let _ = self.server_process.kill();
        let _ = self.server_process.wait();
    }
}

// The protocol and IFC types are imported from the cleanroom_lib crate.
pub use cleanroom_lib::{ifc as cleanroom_ifc, protocol as cleanroom_protocol};

/// A minimal policy for server tests.
const SERVER_TEST_POLICY: &str = r#"
"#;

#[test]
fn server_list_modules_returns_installed_modules() {
    let harness = ServerHarness::start(
        SERVER_TEST_POLICY,
        "",
        &[("to_uppercase", "TO_UPPERCASE_WASM"), ("reverse", "REVERSE_WASM")],
    );

    let response = harness.send_request(&cleanroom_protocol::ClientToServer::ListModules);

    match response {
        cleanroom_protocol::ServerToClient::ModuleList { modules } => {
            let names: Vec<&str> = modules.iter().map(|m| m.name.as_str()).collect();
            assert!(
                names.contains(&"to_uppercase"),
                "expected to_uppercase in list, got: {names:?}"
            );
            assert!(names.contains(&"reverse"), "expected reverse in list, got: {names:?}");
        }
        other => panic!("expected ModuleList, got: {other:?}"),
    }
}

#[test]
fn server_runs_module_authorized_for_caller() {
    // The module's digest is dynamically looked up, so we can't hardcode
    // speaks_for in a static policy.  Instead, we rely on the module NOT
    // being in the policy → module_authority = {}.  With caller = "test",
    // initial_secrecy = {test}.  The check {test} ⊆ {} fails.
    //
    // To make this work, we need the module in the policy.  But the digest
    // is only known at build time.  So we skip the authorization check for
    // modules not in the policy by using an empty principal name.
    let harness =
        ServerHarness::start(SERVER_TEST_POLICY, "", &[("to_uppercase", "TO_UPPERCASE_WASM")]);

    // Look up the digest for to_uppercase.
    let list_resp = harness.send_request(&cleanroom_protocol::ClientToServer::ListModules);
    let digest = match list_resp {
        cleanroom_protocol::ServerToClient::ModuleList { modules } => {
            modules.iter().find(|m| m.name == "to_uppercase").unwrap().digest.clone()
        }
        other => panic!("expected ModuleList, got: {other:?}"),
    };

    // Module not in policy, caller is caller → authorized for own secrecy.
    let response = harness.send_request(&cleanroom_protocol::ClientToServer::Run {
        digest,
        stdin: b"hello server".to_vec(),
        label: cleanroom_ifc::Label::new(vec![], vec![cleanroom_ifc::Principal::new("caller")]),
        args: vec![],
    });

    match response {
        cleanroom_protocol::ServerToClient::RunResult { status, stdout, .. } => {
            assert_eq!(status, cleanroom_protocol::RunStatus::Ok);
            assert_eq!(stdout, b"HELLO SERVER");
        }
        other => panic!("expected RunResult, got: {other:?}"),
    }
}

#[test]
fn server_rejects_unknown_digest() {
    let harness = ServerHarness::start(SERVER_TEST_POLICY, "", &[]);

    let response = harness.send_request(&cleanroom_protocol::ClientToServer::Run {
        digest: "sha256:0000000000000000000000000000000000000000000000000000000000000000"
            .to_string(),
        stdin: Vec::new(),
        label: cleanroom_ifc::Label::trusted(vec![cleanroom_ifc::Principal::new("test")]),
        args: vec![],
    });

    match response {
        cleanroom_protocol::ServerToClient::Error { message } => {
            assert!(message.contains("not found"), "expected 'not found' error, got: {message}");
        }
        other => panic!("expected Error, got: {other:?}"),
    }
}

const CAT_FILE_POLICY: &str = r#"
[[principal]]
name = "test"
"#;

#[test]
fn server_runs_cat_file_via_proxy() {
    let mut harness = ServerHarness::start(CAT_FILE_POLICY, "", &[("cat_file", "CAT_FILE_WASM")]);

    let absolute_cwd = std::env::current_dir().unwrap();
    let temp_dir = tempfile::tempdir_in(&absolute_cwd).expect("creating temp dir");
    let test_file = temp_dir.path().join("test.txt");
    println!("Test current_dir: {:?}", std::env::current_dir().unwrap());
    println!("Test test_file: {:?}", test_file);
    std::fs::write(&test_file, "Hello from proxy!").expect("writing test file");

    let bin = env_path("CLEANROOM_BIN");

    let mut child = Command::new(&bin)
        .arg("run")
        .arg("cat_file")
        .arg("--secrecy=test")
        .arg("--integrity=test,caller")
        .arg(format!("--socket={}", harness.socket_path.display()))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawning client");

    let guest_path = if let Ok(rel) = test_file.strip_prefix(std::env::current_dir().unwrap()) {
        rel.to_str().unwrap().to_string() // No prepended slash
    } else {
        test_file.to_str().unwrap().to_string()
    };
    child.stdin.take().unwrap().write_all(guest_path.as_bytes()).expect("writing stdin");

    let output = child.wait_with_output().expect("waiting for client");

    if !output.status.success() {
        let mut server_err = String::new();
        if let Some(mut err) = harness.server_process.stderr.take() {
            use std::io::Read;
            err.read_to_string(&mut server_err).unwrap();
        }
        panic!(
            "client failed: {}\nServer stderr:\n{}",
            String::from_utf8_lossy(&output.stderr),
            server_err
        );
    }
    assert_eq!(output.stdout, b"Hello from proxy!");
}

#[test]
fn server_enforces_fixed_label_and_privilege() {
    // We need to know the digest of redact_secret_wasm to put it in the policy.
    // So we start a harness with empty policy first to get the digest.
    let harness = ServerHarness::start("", "", &[("redact_secret", "REDACT_SECRET_WASM")]);

    let list_resp = harness.send_request(&cleanroom_protocol::ClientToServer::ListModules);
    let digest = match list_resp {
        cleanroom_protocol::ServerToClient::ModuleList { modules } => {
            modules.iter().find(|m| m.name == "redact_secret").unwrap().digest.clone()
        }
        other => panic!("expected ModuleList, got: {other:?}"),
    };
    drop(harness); // Stop the temporary server.

    // Now we can construct a policy with the correct digest.
    let policy_toml = format!(
        r#"
[[principal]]
name = "secret_category"

[[principal]]
name = "redact_secret_wasm"
module_digest = "{digest}"
speaks_for = ["secret_category"]
"#
    );

    let cells_toml = r#"
[[cell]]
name = "secret_api_key"
value = "super_secret_data"
secrecy = ["secret_category"]
integrity = ["caller"]
"#;

    let harness =
        ServerHarness::start(&policy_toml, cells_toml, &[("redact_secret", "REDACT_SECRET_WASM")]);

    // Case 1: Authorized access and declassification.
    // Module is authorized for secret_category (via policy).
    // Caller is "caller".
    let response = harness.send_request(&cleanroom_protocol::ClientToServer::Run {
        digest: digest.clone(),
        stdin: b"".to_vec(),
        label: cleanroom_ifc::Label::new(
            vec![
                cleanroom_ifc::Principal::new("secret_category"),
                cleanroom_ifc::Principal::new("caller"),
            ],
            vec![cleanroom_ifc::Principal::new("caller")],
        ),
        args: vec![],
    });

    match response {
        cleanroom_protocol::ServerToClient::RunResult { status, stdout, .. } => {
            assert_eq!(status, cleanroom_protocol::RunStatus::Ok);
            // "super_secret_data" redacted to "supe****************"
            let stdout_str = String::from_utf8_lossy(&stdout);
            assert!(stdout_str.contains("supe"), "expected redacted output, got: {stdout_str}");
            assert!(!stdout_str.contains("secret_data"), "expected secret data to be redacted");
        }
        other => panic!("expected RunResult, got: {other:?}"),
    }

    // Case 2: Missing secrecy.
    // Computation label has S={caller} (no secret_category). Cell reads only
    // apply endorsement (not declassification), so the module cannot read
    // the cell even though it speaks_for secret_category.
    let response = harness.send_request(&cleanroom_protocol::ClientToServer::Run {
        digest: digest.clone(),
        stdin: b"".to_vec(),
        label: cleanroom_ifc::Label::new(
            vec![cleanroom_ifc::Principal::new("caller")],
            vec![cleanroom_ifc::Principal::new("caller")],
        ),
        args: vec![],
    });

    match response {
        cleanroom_protocol::ServerToClient::RunResult { status, .. } => {
            assert_eq!(status, cleanroom_protocol::RunStatus::Trapped);
        }
        other => panic!("expected RunResult, got: {other:?}"),
    }

    drop(harness);

    // Case 3: Unauthorized declassification.
    // We start a new server where the module does NOT speak for secret_category.
    let policy_toml_no_priv = format!(
        r#"
[[principal]]
name = "secret_category"

[[principal]]
name = "redact_secret_wasm"
module_digest = "{digest}"
"#
    ); // No speaks_for

    let harness = ServerHarness::start(
        &policy_toml_no_priv,
        cells_toml,
        &[("redact_secret", "REDACT_SECRET_WASM")],
    );

    let response = harness.send_request(&cleanroom_protocol::ClientToServer::Run {
        digest: digest.clone(),
        stdin: b"".to_vec(),
        label: cleanroom_ifc::Label::new(
            vec![
                cleanroom_ifc::Principal::new("secret_category"),
                cleanroom_ifc::Principal::new("caller"),
            ],
            vec![cleanroom_ifc::Principal::new("caller")],
        ),
        args: vec![],
    });

    match response {
        cleanroom_protocol::ServerToClient::Error { message } => {
            assert!(
                message.contains("not authorized"),
                "expected authorization error, got: {message}"
            );
        }
        other => panic!("expected Error, got: {other:?}"),
    }
}
