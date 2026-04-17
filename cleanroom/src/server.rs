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
    ifc::{Label, Principal, Privilege},
    policy::Policy,
    principals::PrincipalsFile,
    protocol::{self, ClientToServer, ModuleInfo, RunStatus, ServerToClient},
};

/// Runs the cleanroom server, listening on the given Unix socket.
///
/// This function blocks until the process is terminated.
pub fn run_server(
    policy_file: Option<&Path>,
    cells_file: Option<&Path>,
    socket_path: &Path,
    module_store: &Path,
) -> Result<()> {
    let mut policy = Policy::default();

    if let Some(cells_path) = cells_file {
        policy.load_cells_file(cells_path).context("loading cells file")?;
    }

    let principals = match policy_file {
        Some(path) => {
            let pf = PrincipalsFile::load(path).context("loading policy file")?;
            log::info!("loaded {} principals from {path:?}", pf.principal.len());
            for p in &pf.principal {
                log::info!("  principal: {}", p.name);
                if let Some(digest) = &p.module_digest {
                    log::info!("    module_digest: {}", digest);
                }
                if !p.speaks_for.is_empty() {
                    log::info!("    speaks_for: {:?}", p.speaks_for);
                }
            }
            pf
        }
        None => {
            log::info!("no policy file, running without identity-based IFC");
            PrincipalsFile::default()
        }
    };

    let manifest = load_manifest(module_store).context("loading module manifest")?;
    log::info!("loaded {} modules from manifest", manifest.len());
    for (name, digest) in &manifest {
        log::info!("  module: {} -> {}", name, digest);
    }

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

        let result = handle_connection(&mut stream, &policy, &manifest, module_store, &principals);
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
    principals: &PrincipalsFile,
) -> Result<()> {
    log::info!("CleanroomState::handle_connection: reading request...");
    let request: ClientToServer = protocol::read_message(stream).context("reading request")?;
    log::info!("CleanroomState::handle_connection: received request: {:?}", request);

    let client_stream = std::sync::Arc::new(std::sync::Mutex::new(
        stream.try_clone().context("cloning client stream")?,
    ));

    let response = match request {
        ClientToServer::Run { digest, stdin, label, args } => {
            log::info!("handling run request for digest \"{}\" with label {}", digest, label);
            let ctx = ConnectionContext {
                policy,
                module_store,
                principals,
                client_stream: Some(client_stream),
            };
            handle_run(&digest, &stdin, &label, &args, ctx)
        }
        ClientToServer::ListModules => handle_list_modules(manifest, policy),
        ClientToServer::QueryPolicy { digest } => handle_query_policy(&digest, policy, principals),
        _ => return Err(anyhow::anyhow!("unexpected request type at top level")),
    };

    protocol::write_message(stream, &response).context("writing response")?;
    Ok(())
}

pub struct ConnectionContext<'a> {
    pub policy: &'a Policy,
    pub module_store: &'a Path,
    pub principals: &'a PrincipalsFile,
    pub client_stream: Option<Arc<Mutex<std::os::unix::net::UnixStream>>>,
}

/// Handles a `Run` request: loads the module, executes it with WASI +
/// IFC, and returns the result.
///
/// **Output enforcement**: the server checks whether the module's
/// computation label flows to the output channel's label.  The
/// channel label is derived from the caller's authority.  If the
/// computation carries categories beyond the channel (i.e. the
/// module didn't fully declassify), stdout is **not** returned.
fn handle_run(
    digest: &str,
    stdin: &[u8],
    requested_label: &Label,
    args: &[String],
    ctx: ConnectionContext,
) -> ServerToClient {
    // Enforce that the computation carries the caller's ambient secrecy.
    // In the future, this will be derived from the socket or peer credentials.
    let mut effective_secrecy = requested_label.secrecy_set().clone();
    effective_secrecy.insert(Principal::new("caller"));
    let effective_label = Label::new(effective_secrecy, requested_label.integrity_set().clone());

    let caller_principals: Vec<Principal> =
        requested_label.integrity_set().iter().cloned().collect();
    let channel_label = if caller_principals.is_empty() {
        Label::public()
    } else {
        // Resolve the full authority chain for each integrity principal.
        let mut full_authority = std::collections::BTreeSet::new();
        for p in &caller_principals {
            full_authority.extend(ctx.principals.resolve_speaks_for(p.name()));
        }
        let authority_vec: Vec<Principal> = full_authority.into_iter().collect();
        Label::new(authority_vec.clone(), authority_vec)
    };

    match execute_module(digest, stdin, &effective_label, args, &channel_label, ctx) {
        Ok((status, stdout, stderr)) => ServerToClient::RunResult { status, stdout, stderr },
        Err(e) => ServerToClient::Error { message: format!("{e:#}") },
    }
}

/// Executes a Wasm module using the Wasmtime Component Model with
/// per-operation IFC privilege.
///
/// The computation label is immutable for the duration of execution.
/// Privilege is exercised per-I/O-operation via the custom
/// `oak:cleanroom/ifc` interface rather than by mutating a global
/// label.
pub fn run_component_module(
    wasm_bytes: &[u8],
    stdin: &[u8],
    args: &[String],
    label: Label,
    privilege: Privilege,
    channel_label: Label,
    ctx: ConnectionContext,
) -> Result<(RunStatus, Vec<u8>, Vec<u8>)> {
    use wasmtime::{
        Engine, Store,
        component::{Component, Linker},
    };
    use wasmtime_wasi::{WasiCtxBuilder, bindings::sync::Command};

    use crate::wasi_ifc::CleanroomState;

    // Initialize Wasmtime Engine and Component Linker.
    let engine = Engine::default();
    let mut linker: Linker<CleanroomState> = Linker::new(&engine);

    wasmtime_wasi::add_to_linker_sync(&mut linker)?;

    // Add custom Cleanroom host bindings for IFC metadata (get-label,
    // read-cell), proxied filesystem access, and IFC-gated HTTP.
    crate::wasi_ifc::Runner::add_to_linker(&mut linker, |s| s)
        .context("adding custom cleanroom bindings to linker")?;

    // Configure the WASI context with standard I/O pipes.
    //
    // Stdin is provided as a memory pipe. Stdout and stderr are
    // captured in memory and released to the caller only if the
    // IFC check passes at module completion.
    let stdout_pipe = wasmtime_wasi::pipe::MemoryOutputPipe::new(usize::MAX);
    let stderr_pipe = wasmtime_wasi::pipe::MemoryOutputPipe::new(usize::MAX);

    let mut ctx_builder = WasiCtxBuilder::new();
    ctx_builder.stdin(wasmtime_wasi::pipe::MemoryInputPipe::new(stdin.to_vec()));
    ctx_builder.stdout(stdout_pipe.clone());
    ctx_builder.stderr(stderr_pipe.clone());

    // WASI args include argv[0] (program name). Prepend one so that
    // clap and std::env::args() don't consume the first real argument.
    let mut wasi_args = vec!["module".to_string()];
    wasi_args.extend_from_slice(args);
    ctx_builder.args(&wasi_args);

    let state = CleanroomState {
        table: wasmtime_wasi::ResourceTable::new(),
        ctx: ctx_builder.build(),
        label: label.clone(),
        policy: std::sync::Arc::new(ctx.policy.clone()),
        privilege: privilege.clone(),
        channel_label: channel_label.clone(),
        client_stream: ctx.client_stream,
    };

    let mut store = Store::new(&engine, state);
    let component =
        Component::from_binary(&engine, wasm_bytes).context("reading component binary")?;

    let instance = linker.instantiate(&mut store, &component).context("instantiating component")?;
    let command = Command::new(&mut store, &instance).context("creating command wrapper")?;

    // Run the module.
    let run_result = command.wasi_cli_run().call_run(&mut store);

    // Extract captured output from WASI pipes.
    drop(store);
    let stdout_bytes: Vec<u8> = stdout_pipe.try_into_inner().unwrap_or_default().into();
    let stderr_bytes: Vec<u8> = stderr_pipe.try_into_inner().unwrap_or_default().into();

    // IFC boundary check: the computation label must flow to the
    // channel label (with module privilege) for output to be released.
    let output_allowed = label.flows_to_declassifying(&channel_label, &privilege).is_ok();

    match run_result {
        Ok(_) => {
            if output_allowed {
                Ok((RunStatus::Ok, stdout_bytes, stderr_bytes))
            } else {
                log::warn!(
                    "IFC: suppressing output — computation label {} \
                     does not flow to channel label {} with module privilege",
                    label,
                    channel_label
                );
                Ok((RunStatus::Ok, Vec::new(), Vec::new()))
            }
        }
        Err(e) => {
            let mut err_output = if output_allowed { stderr_bytes } else { Vec::new() };
            err_output.extend(format!("\nWasmtime trap: {e:#}").into_bytes());
            Ok((RunStatus::Trapped, Vec::new(), err_output))
        }
    }
}

/// Loads and executes a module from the store using its digest, applying policy
/// constraints.
///
/// ## Fixed-label IFC model
///
/// 1. The initial label is the `requested_label` from the caller, which
///    specifies both **secrecy** and **integrity** for the computation.
/// 2. The module must be authorized (via `speaks_for`) for every secrecy
///    principal in the label (except the caller's own identity).
/// 3. The caller's label must flow to the computation label (no spawning at
///    lower secrecy from a more secret environment).
/// 4. Cell reads are access-checked: the cell's label must flow to the
///    computation's label (no implicit taint raising).
fn execute_module(
    digest: &str,
    stdin: &[u8],
    requested_label: &Label,
    args: &[String],
    channel_label: &Label,
    ctx: ConnectionContext,
) -> Result<(RunStatus, Vec<u8>, Vec<u8>)> {
    let wasm_path = resolve_module_path(digest, ctx.module_store)?;
    let wasm_bytes =
        std::fs::read(&wasm_path).with_context(|| format!("reading module at {wasm_path:?}"))?;

    verify_digest(digest, &wasm_bytes)?;

    let initial_label = requested_label.clone();
    log::info!("computation label: {}", initial_label);

    // The caller's identity is the integrity set of the label.
    let caller_integrity = initial_label.integrity_set();

    // Resolve the module's identity to its privilege.
    let module_authority = match ctx.principals.find_by_digest(digest) {
        Some(entry) => {
            let auth = ctx.principals.resolve_speaks_for(&entry.name);
            log::info!("module \"{}\" speaks for: {:?}", entry.name, auth);
            auth
        }
        None => {
            log::info!("module {digest} not in principals file, no privilege");
            std::collections::BTreeSet::new()
        }
    };

    // Authorization check: the module must be authorized for secrecy
    // principals in the label, EXCEPT for the caller's own identities
    // (the integrity set). Any module can operate at the caller's
    // level without requiring explicit authorization.
    let auth_principals: Vec<Principal> = initial_label
        .secrecy_set()
        .iter()
        .filter(|p| !caller_integrity.contains(p))
        .cloned()
        .collect();
    let runtime_label = Label::secret(auth_principals);
    let module_label = Label::secret(module_authority.iter().cloned().collect::<Vec<_>>());
    if let Err(e) = runtime_label.flows_to(&module_label) {
        anyhow::bail!("module not authorized for requested secrecy: {e}");
    }

    let privilege = Privilege::full(module_authority);
    run_component_module(
        &wasm_bytes,
        stdin,
        args,
        initial_label,
        privilege,
        channel_label.clone(),
        ctx,
    )
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

/// Retrieves privilege information for a module based on its
/// principals entry.
fn handle_query_policy(
    digest: &str,
    _policy: &Policy,
    principals: &PrincipalsFile,
) -> ServerToClient {
    match principals.find_by_digest(digest) {
        Some(entry) => {
            let auth = principals.resolve_speaks_for(&entry.name);
            ServerToClient::PolicyInfo {
                can_declassify: auth.into_iter().map(|p| p.name().to_string()).collect(),
            }
        }
        None => ServerToClient::PolicyInfo { can_declassify: vec![] },
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
