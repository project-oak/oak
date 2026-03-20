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
//! A heavily sandboxed WebAssembly runner intended for use by LLM agents.
//!
//! Cleanroom executes an arbitrary Wasm module in a locked-down environment:
//! no filesystem access, no network access, no environment variables, no
//! system calls beyond what is explicitly enabled. The module communicates
//! with the outside world exclusively through stdin and stdout bytes piped
//! through the cleanroom runner.
//!
//! ## ABI
//!
//! Cleanroom reuses the [Oak Functions ABI] — the same ABI used by Oak
//! Functions and Oak Verity — provided by [`oak_functions_service`]. This
//! gives us a battle-tested host runtime with fuel and memory limits,
//! automatic `alloc` export handling, and sandboxed execution via the
//! `wasmtime` JIT.
//!
//! Modules are built with [`oak_functions_sdk`] (or its thin cleanroom
//! wrapper [`cleanroom_sdk`]) which provides `read_request` / `write_response`
//! and exports the required `alloc` symbol.
//!
//! ## Usage
//!
//! ```text
//! echo "hello world" | cleanroom --wasm-module-file=path/to/module.wasm
//! ```
//!
//! All bytes from `stdin` are fed to the module as its request body. The
//! module's response bytes are written to `stdout`. Errors go to `stderr`.
//!
//! [Oak Functions ABI]: https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md

use std::{
    io::{self, Read, Write},
    path::PathBuf,
};

use anyhow::{Context, Result};
use clap::Parser;
use oak_functions_service::{
    instance::OakFunctionsInstance,
    wasm::{WasmConfig, WasmHandler},
};
use oak_proto_rust::oak::functions::InitializeRequest;

/// Command-line arguments for the cleanroom runner.
#[derive(Parser, Debug)]
#[command(
    author,
    version,
    about = "Cleanroom: a sandboxed WebAssembly runner for LLM agents",
    long_about = "Runs a WebAssembly module in a heavily sandboxed environment \
using the Oak Functions ABI. The module has no access to the filesystem, \
network, or environment variables. It communicates exclusively through stdin \
(request bytes) and stdout (response bytes)."
)]
struct Args {
    /// Path to the compiled WebAssembly module file (.wasm).
    #[arg(long, value_name = "FILE")]
    wasm_module_file: PathBuf,
}

fn main() {
    env_logger::init();
    let args = Args::parse();

    if let Err(e) = run(&args) {
        eprintln!("cleanroom error: {e:#}");
        std::process::exit(1);
    }
}

fn run(args: &Args) -> Result<()> {
    // Read the Wasm module from disk.
    let wasm_bytes = std::fs::read(&args.wasm_module_file)
        .with_context(|| format!("reading Wasm module from {:?}", args.wasm_module_file))?;

    // Read the entire stdin as the request body.
    let mut input = Vec::new();
    io::stdin().lock().read_to_end(&mut input).context("reading stdin")?;

    // Create an Oak Functions instance using the Wasmtime backend.
    // WasmConfig::default() applies a sensible set of resource limits (fuel,
    // memory, etc.) that prevent the module from looping forever or allocating
    // unbounded memory.
    let initialize_request =
        InitializeRequest { wasm_module: wasm_bytes, constant_response_size: 0 };

    let instance = OakFunctionsInstance::<WasmHandler>::new(
        &initialize_request,
        None, // No observer.
        WasmConfig::default(),
    )
    .context("creating Oak Functions instance")?;

    // Feed stdin bytes to the module and collect the response.
    let response_bytes = instance.handle_user_request(input).context("executing Wasm module")?;

    // Write the response to stdout.
    io::stdout().lock().write_all(&response_bytes).context("writing output to stdout")?;

    Ok(())
}
