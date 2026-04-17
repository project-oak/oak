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

//! # Cleanroom
//!
//! A sandboxed WebAssembly runner with Information Flow Control (IFC)
//! for humans and LLM agents.

use std::path::PathBuf;

use anyhow::Result;
use clap::{Parser, Subcommand};
use cleanroom_lib::{client, ifc, policy, principals, protocol, server, shell};
use oak_file_utils::resolve_bazel_path;

/// Cleanroom: a sandboxed WebAssembly runner with IFC.
#[derive(Parser, Debug)]
#[command(
    author,
    version,
    about = "Cleanroom: a sandboxed WebAssembly runner with IFC",
    long_about = "Runs WebAssembly modules in a sandboxed environment with \
Information Flow Control. Modules communicate via WASI and are subject to \
declassification policies that prevent unauthorized data exfiltration."
)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Run a Wasm module via the server.
    Run {
        /// Module to run.  Accepts either a human-readable name (e.g.
        /// `weather_wasm`) which is resolved via the server's module
        /// manifest, or a content digest (e.g.
        /// `sha256:3e8b0d72...`) to reference a module directly.
        #[arg(value_name = "NAME|DIGEST")]
        module: String,

        /// Secrecy principals for the computation label.
        ///
        /// The module must be authorized (via speaks_for) for every
        /// principal listed here (beyond the caller's own identity).
        /// Cell reads are access-checked against this label.
        #[arg(long, value_name = "PRINCIPAL", value_delimiter = ',')]
        secrecy: Vec<String>,

        /// Integrity principals for the computation label.
        ///
        /// Identifies the caller: who vouches for stdin data.
        /// The server derives the output channel from this set.
        #[arg(long, value_name = "PRINCIPAL", value_delimiter = ',')]
        integrity: Vec<String>,

        /// Path to the Unix domain socket for the cleanroom server.
        ///
        /// Defaults to `/tmp/cleanroom.sock`, or the value of the
        /// `CLEANROOM_SOCKET` environment variable if set.
        #[arg(
            long,
            value_name = "PATH",
            default_value = "/tmp/cleanroom.sock",
            env = "CLEANROOM_SOCKET"
        )]
        socket: PathBuf,

        /// Arguments to forward to the Wasm module.
        ///
        /// Everything after `--` is forwarded verbatim as WASI
        /// command-line arguments available via `std::env::args()`.
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        module_args: Vec<String>,
    },

    /// List available modules registered with the server.
    Ls {
        /// Path to the Unix domain socket for the cleanroom server.
        #[arg(
            long,
            value_name = "PATH",
            default_value = "/tmp/cleanroom.sock",
            env = "CLEANROOM_SOCKET"
        )]
        socket: PathBuf,
    },

    /// Launch a sandboxed shell with a cleanroom server.
    ///
    /// Starts a cleanroom server on the host, then drops you into a
    /// network-isolated shell.  Inside the shell, use `cleanroom run`
    /// and `cleanroom list` to interact with modules.
    Shell(shell::ShellArgs),

    /// Start the cleanroom IFC server daemon (internal).
    ///
    /// Listens on a Unix domain socket for requests and runs Wasm
    /// modules with WASI + IFC enforcement.  Normally started
    /// automatically by `cleanroom shell`.
    #[command(hide = true)]
    Server {
        /// Path to the policy file (TOML).
        ///
        /// Defines the trust graph: principals, speaks-for
        /// delegations, and module identities.
        #[arg(long, value_name = "FILE")]
        policy_file: Option<PathBuf>,

        /// Path to the cells file (TOML).
        ///
        /// Contains named data cells with IFC labels.  When a module
        /// reads a cell via `get-cell`, its computation label is
        /// tainted with the cell's label.
        #[arg(long, value_name = "FILE")]
        cells_file: Option<PathBuf>,

        /// Path to the Unix domain socket to listen on.
        #[arg(long, value_name = "PATH")]
        socket: PathBuf,

        /// Path to the content-addressed module store directory.
        ///
        /// Must contain a `manifest.toml` mapping module names to
        /// digests, and a `sha256/` subdirectory with the module
        /// binaries.
        #[arg(long, value_name = "DIR")]
        module_store: PathBuf,
    },

    /// Run a Wasm module directly (no server).
    ///
    /// Used for testing and local development.  Runs a single module
    /// with WASI + IFC in-process.
    #[command(hide = true, name = "run-local")]
    RunLocal {
        #[arg(value_name = "FILE")]
        wasm_module_file: PathBuf,

        /// Path to the policy file (TOML).
        #[arg(long, value_name = "FILE")]
        policy_file: Option<PathBuf>,

        /// Arguments to forward to the Wasm module.
        ///
        /// Everything after `--` is forwarded verbatim as WASI
        /// command-line arguments available via `std::env::args()`.
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        module_args: Vec<String>,
    },

    /// Manage the trust graph (principals and delegations).
    Principal {
        /// Path to the principals file.
        #[arg(long, default_value = "principals.toml")]
        file: PathBuf,

        #[command(subcommand)]
        action: PrincipalAction,
    },
}

#[derive(Subcommand, Debug)]
enum PrincipalAction {
    /// Add a principal (named, SSH key, or module).
    Add {
        /// Human-readable name.
        #[arg(long)]
        name: String,

        /// Path to SSH public key file (creates an SSH key principal).
        #[arg(long, conflicts_with = "module_digest")]
        key: Option<PathBuf>,

        /// Module content digest (creates a module principal).
        #[arg(long, conflicts_with = "key")]
        module_digest: Option<String>,
    },

    /// List all registered principals and delegations.
    List,

    /// Add a speaks-for edge: --to speaks for --from.
    Delegate {
        /// Name of the principal granting authority.
        #[arg(long)]
        from: String,

        /// Name of the principal receiving authority.
        #[arg(long)]
        to: String,
    },

    /// Remove a speaks-for edge.
    Revoke {
        /// Name of the principal whose authority is revoked.
        #[arg(long)]
        from: String,

        /// Name of the principal losing the delegation.
        #[arg(long)]
        to: String,
    },
}

fn main() {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();
    let args = Args::parse();

    let result = match args.command {
        Command::Run { module, secrecy, integrity, socket, module_args } => {
            let socket = resolve_bazel_path(socket);
            let label = crate::ifc::Label::new(
                secrecy.iter().map(crate::ifc::Principal::new),
                integrity.iter().map(crate::ifc::Principal::new),
            );
            client::client_run(&socket, &module, label, module_args)
        }
        Command::Ls { socket } => {
            let socket = resolve_bazel_path(socket);
            client::client_list(&socket)
        }
        Command::Shell(ref shell_args) => shell::run_shell(shell_args),
        Command::Server { policy_file, cells_file, socket, module_store } => {
            let policy_file = policy_file.map(resolve_bazel_path);
            let cells_file = cells_file.map(resolve_bazel_path);
            let module_store = resolve_bazel_path(module_store);
            let socket = resolve_bazel_path(socket);
            server::run_server(
                policy_file.as_deref(),
                cells_file.as_deref(),
                &socket,
                &module_store,
            )
        }
        Command::RunLocal { wasm_module_file, policy_file, module_args } => {
            let wasm_module_file = resolve_bazel_path(wasm_module_file);
            let policy_file = policy_file.map(resolve_bazel_path);
            run_local(&wasm_module_file, policy_file.as_deref(), &module_args)
        }
        Command::Principal { file, action } => {
            let file = resolve_bazel_path(file);
            run_principal_action(&file, action)
        }
    };

    if let Err(e) = result {
        eprintln!("cleanroom error: {e:#}");
        std::process::exit(1);
    }
}

/// Runs a Wasm module directly (in-process, no server).
fn run_local(
    wasm_module_file: &std::path::Path,
    policy_file: Option<&std::path::Path>,
    module_args: &[String],
) -> Result<()> {
    use anyhow::Context;

    let policy = if let Some(path) = policy_file {
        policy::Policy::from_file(path).context("loading policy file")?
    } else {
        policy::Policy::default()
    };
    let wasm_bytes = std::fs::read(wasm_module_file)
        .with_context(|| format!("reading wasm file at {}", wasm_module_file.display()))?;

    let mut stdin = Vec::new();
    use std::io::Read;
    std::io::stdin().read_to_end(&mut stdin).context("reading stdin")?;

    let ctx = server::ConnectionContext {
        policy: &policy,
        module_store: std::path::Path::new(""),
        principals: &principals::PrincipalsFile::default(),
        client_stream: None,
    };
    let (status, stdout, stderr) = server::run_component_module(
        &wasm_bytes,
        &stdin,
        module_args,
        ifc::Label::public(),
        ifc::Privilege::none(),
        ifc::Label::public(),
        ctx,
    )?;

    use std::io::Write;
    std::io::stdout().write_all(&stdout).context("writing stdout")?;
    std::io::stderr().write_all(&stderr).context("writing stderr")?;

    if status == protocol::RunStatus::Ok {
        Ok(())
    } else {
        Err(anyhow::anyhow!("Run failed with status {:?}", status))
    }
}

/// Handles `cleanroom principal` subcommands.
fn run_principal_action(file: &std::path::Path, action: PrincipalAction) -> Result<()> {
    use anyhow::Context;

    match action {
        PrincipalAction::Add { name, key, module_digest } => {
            let key = key.map(resolve_bazel_path);
            let mut pf =
                principals::PrincipalsFile::load(file).context("loading principals file")?;

            let ssh_public_key = if let Some(key_path) = key {
                Some(
                    principals::ssh_public_key_from_file(&key_path)
                        .context("reading SSH public key")?,
                )
            } else {
                None
            };

            let entry = principals::PrincipalEntry {
                name: name.clone(),
                ssh_public_key,
                module_digest,
                speaks_for: vec![],
            };

            pf.add_principal(entry)?;
            pf.save(file).context("saving principals file")?;

            let kind = pf.find_by_name(&name).unwrap().kind();
            println!("added {kind} principal \"{name}\"");
            Ok(())
        }

        PrincipalAction::List => {
            let pf = principals::PrincipalsFile::load(file).context("loading principals file")?;

            if pf.principal.is_empty() {
                println!("No principals registered.");
                return Ok(());
            }

            println!("{:<20} {:<8} SPEAKS FOR", "NAME", "TYPE");
            println!("{}", "-".repeat(60));
            for entry in &pf.principal {
                let speaks_for = if entry.speaks_for.is_empty() {
                    "—".to_string()
                } else {
                    entry.speaks_for.join(", ")
                };
                println!("{:<20} {:<8} {}", entry.name, entry.kind(), speaks_for);
            }
            Ok(())
        }

        PrincipalAction::Delegate { from, to } => {
            let mut pf =
                principals::PrincipalsFile::load(file).context("loading principals file")?;
            pf.add_delegation(&from, &to)?;
            pf.save(file).context("saving principals file")?;
            println!("\"{to}\" now speaks for \"{from}\"");
            Ok(())
        }

        PrincipalAction::Revoke { from, to } => {
            let mut pf =
                principals::PrincipalsFile::load(file).context("loading principals file")?;
            pf.remove_delegation(&from, &to)?;
            pf.save(file).context("saving principals file")?;
            println!("revoked: \"{to}\" no longer speaks for \"{from}\"");
            Ok(())
        }
    }
}
