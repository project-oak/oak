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

//! Cleanroom client logic.
//!
//! Connects to the cleanroom server over a Unix domain socket, sends
//! requests, and displays results.

use std::{
    io::{self, Read, Write},
    os::unix::net::UnixStream,
    path::Path,
};

use anyhow::{Context, Result};

use crate::protocol::{self, ClientToServer, ModuleInfo, RunStatus, ServerToClient};

/// Connects to the server, runs a module, and prints the output.
pub fn client_run(socket_path: &Path, module: &str) -> Result<()> {
    use std::io::IsTerminal;

    // Read stdin.
    let mut stdin_bytes = Vec::new();
    if !io::stdin().is_terminal() {
        io::stdin().lock().read_to_end(&mut stdin_bytes).context("reading stdin")?;
    }

    // The module argument could be a name or a digest. If it contains
    // a colon, treat it as a digest; otherwise query the server to
    // resolve the name.
    let digest = if module.contains(':') {
        module.to_string()
    } else {
        resolve_module_name(socket_path, module)?
    };

    // Connect and send the Run request.
    let mut stream = UnixStream::connect(socket_path).context("connecting to cleanroom server")?;

    let request = ClientToServer::Run { digest: digest.clone(), stdin: stdin_bytes };
    protocol::write_message(&mut stream, &request).context("sending request")?;

    loop {
        let response: ServerToClient =
            protocol::read_message(&mut stream).context("reading response")?;

        match response {
            ServerToClient::FsReadFile { path } => {
                log::info!("ThinClient: server requested FsReadFile for path={}", path);
                let data = std::fs::read(&path).unwrap_or_default();
                let reply = ClientToServer::FsReadFileResult { data };
                protocol::write_message(&mut stream, &reply).context("sending FsReadFileResult")?;
            }
            ServerToClient::FsWriteFile { path, data } => {
                log::info!("ThinClient: server requested FsWriteFile for path={}", path);
                let success = std::fs::write(&path, data).is_ok();
                let reply = ClientToServer::FsWriteFileResult { success };
                protocol::write_message(&mut stream, &reply)
                    .context("sending FsWriteFileResult")?;
            }
            ServerToClient::FsDeleteFile { path } => {
                log::info!("ThinClient: server requested FsDeleteFile for path={}", path);
                let success = std::fs::remove_file(&path).is_ok();
                let reply = ClientToServer::FsDeleteFileResult { success };
                protocol::write_message(&mut stream, &reply)
                    .context("sending FsDeleteFileResult")?;
            }
            ServerToClient::FsListDirectory { path } => {
                log::info!("ThinClient: server requested FsListDirectory for path={}", path);
                let entries = std::fs::read_dir(&path)
                    .map(|dir| {
                        dir.filter_map(|e| {
                            e.ok().map(|e| e.file_name().to_string_lossy().into_owned())
                        })
                        .collect()
                    })
                    .unwrap_or_else(|_| Vec::new());
                let reply = ClientToServer::FsListDirectoryResult { entries };
                protocol::write_message(&mut stream, &reply)
                    .context("sending FsListDirectoryResult")?;
            }
            ServerToClient::RunResult { status, stdout, stderr, .. } => {
                // Write stderr first (so it appears before stdout in the terminal).
                if !stderr.is_empty() {
                    io::stderr().lock().write_all(&stderr).context("writing stderr")?;
                }

                // Write stdout.
                io::stdout().lock().write_all(&stdout).context("writing stdout")?;

                match status {
                    RunStatus::Ok => return Ok(()),
                    RunStatus::Trapped => {
                        eprintln!("cleanroom: module execution trapped");
                        std::process::exit(2);
                    }
                    RunStatus::PolicyDenied => {
                        eprintln!("cleanroom: module denied by policy");
                        std::process::exit(3);
                    }
                }
            }
            ServerToClient::Error { message } => {
                anyhow::bail!("server error: {message}");
            }
            _ => {
                anyhow::bail!("unexpected response type from server");
            }
        }
    }
}

fn connect_and_exchange(socket_path: &Path, req: &ClientToServer) -> Result<ServerToClient> {
    let mut stream = UnixStream::connect(socket_path).context("connecting to cleanroom server")?;
    protocol::write_message(&mut stream, req).context("sending request")?;
    protocol::read_message(&mut stream).context("reading response")
}

/// Resolves a module name to a digest by querying the server's module
/// list.
fn resolve_module_name(socket_path: &Path, name: &str) -> Result<String> {
    let response = connect_and_exchange(socket_path, &ClientToServer::ListModules)?;

    match response {
        ServerToClient::ModuleList { modules } => {
            let found = modules.iter().find(|m| m.name == name);
            match found {
                Some(info) => Ok(info.digest.clone()),
                None => {
                    let available: Vec<&str> = modules.iter().map(|m| m.name.as_str()).collect();
                    anyhow::bail!(
                        "module '{name}' not found. Available: {}",
                        if available.is_empty() {
                            "(none)".to_string()
                        } else {
                            available.join(", ")
                        }
                    );
                }
            }
        }
        ServerToClient::Error { message } => anyhow::bail!("server error: {message}"),
        _ => anyhow::bail!("unexpected response type"),
    }
}

/// Lists available modules from the server.
pub fn client_list(socket_path: &Path) -> Result<()> {
    let response = connect_and_exchange(socket_path, &ClientToServer::ListModules)?;

    match response {
        ServerToClient::ModuleList { modules } => {
            if modules.is_empty() {
                println!("No modules registered.");
            } else {
                println!("{:<30} DIGEST", "NAME");
                println!("{}", "-".repeat(70));
                // Sort by name for consistent output.
                let mut sorted: Vec<&ModuleInfo> = modules.iter().collect();
                sorted.sort_by_key(|m| &m.name);
                for m in sorted {
                    println!("{:<30} {}", m.name, m.digest);
                }
            }
            Ok(())
        }
        ServerToClient::Error { message } => anyhow::bail!("server error: {message}"),
        _ => anyhow::bail!("unexpected response type"),
    }
}
