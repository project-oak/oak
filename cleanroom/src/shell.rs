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

//! `cleanroom shell` — launches a sandboxed shell with the cleanroom
//! thin client.
//!
//! This subcommand:
//!
//! 1. Starts a `cleanroom server` daemon on the host.
//! 2. Launches an isolated shell using one of:
//!    - **`sandbox`** (macOS): uses `sandbox-exec` to deny IP networking while
//!      allowing Unix domain sockets (for the cleanroom protocol).
//!    - **`docker` / `podman`**: full container isolation with `--network=none`
//!      and volume mounts.
//! 3. Drops the user into an interactive shell.
//! 4. Tears down the daemon when the shell exits.
//!
//! ## macOS sandbox profile
//!
//! The `sandbox` runtime uses Apple's Seatbelt sandbox
//! (<https://reverse.put.as/wp-content/uploads/2011/09/Apple-Sandbox-Guide-v1.0.pdf>)
//! with a minimal profile that blocks all IP-based networking while
//! permitting everything else (including Unix domain sockets). This is
//! sufficient to demonstrate that modules cannot phone home, while
//! keeping the cleanroom socket functional.

use std::{
    path::{Path, PathBuf},
    process::{Child, Command, Stdio},
};

use anyhow::{Context, Result, bail};
use clap::Parser;

/// Arguments for the `shell` subcommand.
#[derive(Parser, Debug)]
pub struct ShellArgs {
    /// Path to the workspace (repo) directory on the host. If not specified,
    /// defaults to the current directory, or the workspace directory if run via
    /// `bazel run`.
    #[arg(long, value_name = "DIR")]
    pub workspace: Option<PathBuf>,

    /// Path to the policy file (TOML). If not specified, auto-detects
    /// `cleanroom/example_policy.toml` relative to workspace.
    ///
    /// Defines the trust graph: principals, speaks-for delegations,
    /// and module identities.
    #[arg(long, value_name = "FILE")]
    pub policy_file: Option<PathBuf>,

    /// Path to the cells file (TOML). If not specified, defaults to
    /// `cleanroom/example_cells.toml` relative to workspace.
    #[arg(long, value_name = "FILE")]
    pub cells_file: Option<PathBuf>,

    /// Path to the module store directory. If not specified, defaults to
    /// `cleanroom/modules` relative to workspace.
    #[arg(long, value_name = "DIR")]
    pub module_store: Option<PathBuf>,
}

/// Runs the `cleanroom shell` subcommand.
pub fn run_shell(args: &ShellArgs) -> Result<()> {
    // Determine the base workspace directory.
    let workspace_base = args
        .workspace
        .clone()
        .or_else(|| std::env::var("BUILD_WORKSPACE_DIRECTORY").map(PathBuf::from).ok())
        .unwrap_or_else(|| PathBuf::from("."));

    // Resolve absolute path.
    let workspace = std::fs::canonicalize(&workspace_base)
        .with_context(|| format!("resolving workspace path {:?}", workspace_base))?;

    let policy_file = match &args.policy_file {
        Some(path) => Some(
            std::fs::canonicalize(path)
                .with_context(|| format!("resolving policy file {:?}", path))?,
        ),
        None => {
            // Auto-detect: look for the policy file in the workspace.
            let default_path = workspace.join("cleanroom/example_policy.toml");
            if default_path.exists() {
                log::info!("auto-detected policy file at {default_path:?}");
                Some(default_path)
            } else {
                None
            }
        }
    };

    let cells_file = match &args.cells_file {
        Some(path) => std::fs::canonicalize(path)
            .with_context(|| format!("resolving cells file {:?}", path))?,
        None => workspace.join("cleanroom/example_cells.toml"),
    };

    let module_store = match &args.module_store {
        Some(path) => std::fs::canonicalize(path)
            .with_context(|| format!("resolving module store {:?}", path))?,
        None => PathBuf::from("/tmp/modules"),
    };

    // Create a temporary directory for the Unix socket.
    let socket_dir = tempfile::tempdir().context("creating temporary socket directory")?;
    let socket_path = socket_dir.path().join("cleanroom.sock");

    // Resolve the path to the current binary (used as the thin client).
    let self_binary = std::env::current_exe().context("resolving current executable path")?;

    // Start the server daemon.
    log::info!("starting cleanroom server on {socket_path:?}");
    let mut server = start_server(
        &workspace,
        &self_binary,
        policy_file.as_deref(),
        &cells_file,
        &socket_path,
        &module_store,
    )?;

    // Wait briefly for the server to start listening.
    std::thread::sleep(std::time::Duration::from_millis(200));

    // Launch the shell using macOS sandbox-exec.
    let shell_result = run_sandbox_shell(&workspace, &socket_path, &self_binary);

    // Tear down the server regardless of shell exit status.
    log::info!("shutting down cleanroom server");
    let _ = server.kill();
    let _ = server.wait();

    // Clean up the socket.
    drop(socket_dir);

    shell_result
}

/// Starts the cleanroom server as a background process.
fn start_server(
    workspace: &Path,
    binary: &Path,
    policy_file: Option<&Path>,
    cells_file: &Path,
    socket_path: &Path,
    module_store: &Path,
) -> Result<Child> {
    let mut cmd = Command::new(binary);
    cmd.arg("server")
        .arg(format!("--cells-file={}", cells_file.display()))
        .arg(format!("--socket={}", socket_path.display()))
        .arg(format!("--module-store={}", module_store.display()));

    if let Some(path) = policy_file {
        cmd.arg(format!("--policy-file={}", path.display()));
    }

    cmd.current_dir(workspace)
        .stdin(Stdio::null())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn()
        .context("starting cleanroom server")
}

fn run_sandbox_shell(workspace: &Path, socket_path: &Path, client_binary: &Path) -> Result<()> {
    // Resolve the user's preferred shell, falling back to /bin/bash.
    let shell = std::env::var("SHELL").unwrap_or_else(|_| "/bin/bash".to_string());

    // Build a PATH that includes the cleanroom binary's directory so
    // the user can just type `cleanroom client ...`.
    let client_dir = client_binary.parent().unwrap_or(Path::new("/usr/local/bin"));
    let existing_path = std::env::var("PATH").unwrap_or_default();
    let new_path = format!("{}:{}", client_dir.display(), existing_path);

    // Build the macOS Seatbelt profile dynamically.
    let sandbox_profile = format!(
        r#"(version 1)
(allow default)
(deny network-outbound (remote ip))
(deny network-inbound)
(deny file-write*)
(allow file-write* (subpath "{}"))
(allow file-write* (regex #"^/dev/tty"))
"#,
        workspace.display()
    );

    eprintln!("┌─────────────────────────────────────────────────┐");
    eprintln!("│  cleanroom shell (sandbox-exec, no IP network)  │");
    eprintln!("│  Socket: {:<39} │", socket_path.display());
    eprintln!("│  Type `exit` to leave.                          │");
    eprintln!("├─────────────────────────────────────────────────┤");
    eprintln!("│  Applied Sandbox Profile:                       │");
    for line in sandbox_profile.lines() {
        eprintln!("│    {:<43}  │", line);
    }
    eprintln!("└─────────────────────────────────────────────────┘");

    let mut cmd = Command::new("sandbox-exec");
    cmd.arg("-p")
        .arg(&sandbox_profile)
        .arg(&shell)
        .env("CLEANROOM_SOCKET", socket_path)
        .env("PATH", &new_path)
        .current_dir(workspace)
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());

    let status = cmd.status().context("running sandbox-exec")?;

    if !status.success() {
        bail!("sandboxed shell exited with status {status}");
    }

    Ok(())
}
