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

//! Cleanroom IFC server.
//!
//! Listens on a Unix domain socket for [`ClientToServer`] messages from the
//! thin client, runs Wasm modules in wasmtime with WASI, tracks IFC
//! labels, and returns [`ServerToClient`] messages.
//!
//! # Module resolution
//!
//! Modules are stored in a content-addressed directory:
//!
//! ```text
//! <module_store>/
//!   sha256/
//!     <hex-digest> → .wasm file
//!   manifest.toml
//! ```
//!
//! The manifest maps human-readable names to digests.

use std::{
    collections::HashMap,
    os::unix::net::UnixListener,
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
};

use anyhow::{Context, Result, bail};
use sha2::{Digest, Sha256};

use crate::{
    ifc::{ComputationLabel, Label},
    policy::Policy,
    protocol::{self, ClientToServer, ModuleInfo, RunStatus, ServerToClient},
};

/// Runs the cleanroom server, listening on the given Unix socket.
///
/// This function blocks until the process is terminated.
pub fn run_server(
    policy_file: &Path,
    cells_file: Option<&Path>,
    socket_path: &Path,
    module_store: &Path,
) -> Result<()> {
    let mut policy = Policy::from_file(policy_file).context("loading policy file")?;

    if let Some(cells_path) = cells_file {
        policy.load_cells_file(cells_path).context("loading cells file")?;
    }

    let manifest = load_manifest(module_store).context("loading module manifest")?;

    // Remove stale socket file if it exists.
    if socket_path.exists() {
        std::fs::remove_file(socket_path).context("removing stale socket")?;
    }

    let listener = UnixListener::bind(socket_path).context("binding Unix socket")?;

    log::info!("cleanroom server listening on {socket_path:?}");

    for stream in listener.incoming() {
        log::info!("CleanroomState::run_server: received connection, handling...");
        let mut stream = match stream {
            Ok(s) => s,
            Err(e) => {
                log::error!("accepting connection: {e}");
                continue;
            }
        };

        let result = handle_connection(&mut stream, &policy, &manifest, module_store);
        if let Err(e) = result {
            log::error!("CleanroomState::run_server: error handling connection: {e:#}");
            // Try to send an error response.
            let _ = protocol::write_message(
                &mut stream,
                &ServerToClient::Error { message: format!("{e:#}") },
            );
        }
    }

    Ok(())
}

fn handle_connection(
    stream: &mut std::os::unix::net::UnixStream,
    policy: &Policy,
    manifest: &HashMap<String, String>,
    module_store: &Path,
) -> Result<()> {
    log::info!("CleanroomState::handle_connection: reading request...");
    let request: ClientToServer = protocol::read_message(stream).context("reading request")?;
    log::info!("CleanroomState::handle_connection: received request: {:?}", request);

    let client_stream = std::sync::Arc::new(std::sync::Mutex::new(
        stream.try_clone().context("cloning client stream")?,
    ));

    let response = match request {
        ClientToServer::Run { digest, stdin } => {
            handle_run(&digest, &stdin, policy, module_store, Some(client_stream))
        }
        ClientToServer::ListModules => handle_list_modules(manifest, policy),
        ClientToServer::QueryPolicy { digest } => handle_query_policy(&digest, policy),
        _ => return Err(anyhow::anyhow!("unexpected request type at top level")),
    };

    protocol::write_message(stream, &response).context("writing response")?;
    Ok(())
}

/// Handles a `Run` request: loads the module, executes it with WASI +
/// IFC, and returns the result.
///
/// **Output enforcement**: the server checks whether the module's
/// computation label flows to the output channel's label.  The
/// channel label is `{local_repo}` because the client runs inside
/// the repo sandbox and already has access to local data.  If the
/// computation carries categories beyond `local_repo` (e.g.
/// `secret_category`), stdout is **not** returned — the module must
/// declassify those categories first.
fn handle_run(
    digest: &str,
    stdin: &[u8],
    policy: &Policy,
    module_store: &Path,
    client_stream: Option<Arc<Mutex<std::os::unix::net::UnixStream>>>,
) -> ServerToClient {
    // The client lives inside the repo sandbox, so it already has
    // local_repo-level data.  Output can flow there without
    // declassification.
    let channel_label = Label::category("local_repo");

    match execute_module(digest, stdin, policy, module_store, client_stream) {
        Ok((status, output_label, stdout, stderr)) => {
            if let Err(excess) = output_label.flows_to(&channel_label) {
                // Output is tainted — block stdout.
                log::warn!("blocking tainted output from module {digest}: {excess}");
                ServerToClient::RunResult {
                    status: RunStatus::Trapped,
                    stdout: Vec::new(),
                    stderr: format!(
                        "output blocked: computation is tainted with [{excess}]; \
                         call declassify() first\n",
                    )
                    .into_bytes(),
                }
            } else {
                // Computation label flows to channel — safe to return.
                ServerToClient::RunResult { status, stdout, stderr }
            }
        }
        Err(e) => ServerToClient::Error { message: format!("{e:#}") },
    }
}

/// Executes a Wasm module using the Wasmtime Component Model with IFC tracking.
pub fn run_component_module(
    wasm_bytes: &[u8],
    policy: &crate::policy::Policy,
    stdin: &[u8],
    pc: &Arc<Mutex<ComputationLabel>>,
    privilege: crate::ifc::DeclassificationPrivilege,
    client_stream: Option<Arc<Mutex<std::os::unix::net::UnixStream>>>,
) -> Result<(RunStatus, Label, Vec<u8>, Vec<u8>)> {
    use wasmtime::{
        Engine, Store,
        component::{Component, Linker},
    };
    use wasmtime_wasi::{WasiCtxBuilder, bindings::sync::Command};

    use crate::wasi_ifc::CleanroomState;

    // Initialize Wasmtime Engine and Component Linker.
    let engine = Engine::default();
    let mut linker: Linker<CleanroomState> = Linker::new(&engine);

    // Add standard WASI interfaces (clocks, random number generation, etc.).
    wasmtime_wasi::add_to_linker_sync(&mut linker)?;

    wasmtime_wasi_http::add_only_http_to_linker_sync(&mut linker)
        .context("adding outgoing HTTP to component linker")?;

    // Add custom Cleanroom host bindings for IFC tracking and proxied filesystem
    // access.
    crate::wasi_ifc::Runner::add_to_linker(&mut linker, |s| s)
        .context("adding custom cleanroom bindings to linker")?;

    // Configure the WASI context.
    //
    // No direct filesystem preopens are provided. Modules must access files
    // exclusively through the custom `oak:cleanroom/fs` interface, which
    // proxies I/O operations through the client stream to the host file system.
    let mut ctx_builder = WasiCtxBuilder::new();

    let stdout_pipe = wasmtime_wasi::pipe::MemoryOutputPipe::new(1024 * 1024); // 1MB buffer
    let stderr_pipe = wasmtime_wasi::pipe::MemoryOutputPipe::new(1024 * 1024); // 1MB buffer
    ctx_builder.stdin(wasmtime_wasi::pipe::MemoryInputPipe::new(stdin.to_vec()));
    ctx_builder.stdout(stdout_pipe.clone());
    ctx_builder.stderr(stderr_pipe.clone());

    let state = CleanroomState {
        table: wasmtime_wasi::ResourceTable::new(),
        ctx: ctx_builder.build(),
        http_ctx: wasmtime_wasi_http::WasiHttpCtx::new(),
        pc: Arc::clone(pc),
        policy: std::sync::Arc::new(policy.clone()),
        privilege,
        client_stream,
    };

    let mut store = Store::new(&engine, state);
    let component =
        Component::from_binary(&engine, wasm_bytes).context("reading component binary")?;

    let instance = linker.instantiate(&mut store, &component).context("instantiating component")?;

    let command = Command::new(&mut store, &instance).context("creating command wrapper")?;

    match command.wasi_cli_run().call_run(&mut store) {
        Ok(_) => {
            let stdout_bytes = stdout_pipe.contents().to_vec();
            let stderr_bytes = stderr_pipe.contents().to_vec();
            Ok((
                RunStatus::Ok,
                pc.lock().unwrap().current_label().clone(),
                stdout_bytes,
                stderr_bytes,
            ))
        }
        Err(e) => {
            let mut stderr_bytes = stderr_pipe.contents().to_vec();
            stderr_bytes.extend(format!("\nWasmtime trap: {e:#}").into_bytes());
            Ok((
                RunStatus::Trapped,
                pc.lock().unwrap().current_label().clone(),
                Vec::new(),
                stderr_bytes,
            ))
        }
    }
}

/// Loads and executes a module from the store using its digest, applying policy
/// constraints.
fn execute_module(
    digest: &str,
    stdin: &[u8],
    policy: &Policy,
    module_store: &Path,
    client_stream: Option<Arc<Mutex<std::os::unix::net::UnixStream>>>,
) -> Result<(RunStatus, Label, Vec<u8>, Vec<u8>)> {
    let wasm_path = resolve_module_path(digest, module_store)?;
    let wasm_bytes =
        std::fs::read(&wasm_path).with_context(|| format!("reading module at {wasm_path:?}"))?;

    verify_digest(digest, &wasm_bytes)?;

    let module_policy = policy.module_by_digest(digest);
    if module_policy.is_none() {
        log::warn!("Module {digest} is not listed in policy, proceeding with pure sandbox");
    }

    let privilege = module_policy
        .map(|m| m.privilege.clone())
        .unwrap_or_else(crate::ifc::DeclassificationPrivilege::none);

    let pc = Arc::new(Mutex::new(ComputationLabel::untainted()));
    run_component_module(&wasm_bytes, policy, stdin, &pc, privilege, client_stream)
}

/// Resolves a module digest to its absolute path within the module store.
fn resolve_module_path(digest: &str, module_store: &Path) -> Result<PathBuf> {
    let (algo, hash) =
        digest.split_once(':').context("invalid digest format, expected algorithm:hex")?;

    let path = module_store.join(algo).join(hash);
    if !path.exists() {
        bail!("Module not found in store: {digest}");
    }
    Ok(path)
}

/// Verifies that the computed digest of Wasm bytes matches the expected digest.
fn verify_digest(digest: &str, wasm_bytes: &[u8]) -> Result<()> {
    let (algo, expected_hex) = digest.split_once(':').context("invalid digest format")?;

    match algo {
        "sha256" => {
            let actual = Sha256::digest(wasm_bytes);
            let actual_hex = hex::encode(actual);
            if actual_hex != expected_hex {
                bail!("Digest mismatch: expected {digest}, got sha256:{actual_hex}");
            }
            Ok(())
        }
        _ => bail!("Unsupported digest algorithm: {algo}"),
    }
}

/// Lists all modules available in the manifest.
fn handle_list_modules(manifest: &HashMap<String, String>, _policy: &Policy) -> ServerToClient {
    let modules: Vec<ModuleInfo> = manifest
        .iter()
        .map(|(name, digest)| ModuleInfo { name: name.clone(), digest: digest.clone() })
        .collect();

    ServerToClient::ModuleList { modules }
}

/// Retrieves policy configuration (e.g., declassification privileges) for a
/// given module digest.
fn handle_query_policy(digest: &str, policy: &Policy) -> ServerToClient {
    match policy.module_by_digest(digest) {
        Some(m) => ServerToClient::PolicyInfo {
            can_declassify: m.privilege.as_set().iter().cloned().collect(),
        },
        None => ServerToClient::Error { message: format!("Module {digest} not found in policy") },
    }
}

/// Loads the module manifest from the store directory.
///
/// The manifest is a TOML file mapping names to digests:
///
/// ```toml
/// [modules]
/// crate_vendor = "sha256:aaa..."
/// ```
fn load_manifest(module_store: &Path) -> Result<HashMap<String, String>> {
    let manifest_path = module_store.join("manifest.toml");
    if !manifest_path.exists() {
        return Ok(HashMap::new());
    }

    let contents = std::fs::read_to_string(&manifest_path)
        .with_context(|| format!("reading manifest at {manifest_path:?}"))?;

    #[derive(serde::Deserialize)]
    struct Manifest {
        #[serde(default)]
        modules: HashMap<String, String>,
    }

    let manifest: Manifest = toml::from_str(&contents).context("parsing manifest TOML")?;

    Ok(manifest.modules)
}
