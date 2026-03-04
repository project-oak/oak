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

//! Falsify Wasm runner.
//!
//! Loads a Wasm module implementing a [`falsify::Claim`] (compiled with
//! `falsify_wasm_sdk`) and evaluates it against an input file. The Wasm module
//! is executed using [`OakFunctionsInstance`] — the same infrastructure as
//! Oak Functions and Oak Verity.
//!
//! The result is written to a TOML output file using the same
//! [`falsify::Status`] format as the native `falsify` harness.

use std::{fs, path::PathBuf};

use anyhow::{Context, Result, anyhow};
use clap::Parser;
use log::info;
use oak_functions_service::{
    instance::OakFunctionsInstance,
    wasm::{WasmConfig, WasmHandler},
};
use oak_proto_rust::oak::functions::InitializeRequest;

#[derive(Parser, Debug)]
#[command(author, version, about = "Falsify Wasm runner")]
struct Args {
    /// Path to the compiled Wasm module (.wasm file).
    #[arg(long)]
    wasm_module: PathBuf,

    /// Path to the input file containing the test payload.
    #[arg(long)]
    input_file: PathBuf,

    /// Path for the TOML output file.
    #[arg(long)]
    output_file_toml: PathBuf,
}

fn main() {
    env_logger::init();
    let args = Args::parse();

    let result = run(&args);

    let falsify_result = match result {
        Ok(status) => falsify_native::FalsifyResult { status },
        Err(e) => falsify_native::FalsifyResult {
            status: falsify_native::Status::ClaimError { error_message: format!("{e:#}") },
        },
    };

    let toml_string =
        toml::to_string_pretty(&falsify_result).expect("Could not serialize result to TOML");
    fs::write(&args.output_file_toml, toml_string).expect("Could not write to output file");
}

fn run(args: &Args) -> Result<falsify_native::Status> {
    let input_bytes = fs::read(&args.input_file).context("Could not read input file")?;
    let wasm_bytes = fs::read(&args.wasm_module).context("Could not read Wasm module")?;

    // Use OakFunctionsInstance — the same infrastructure as Oak Functions and
    // Oak Verity — to execute the Wasm module.
    let initialize_request =
        InitializeRequest { wasm_module: wasm_bytes, constant_response_size: 0 };

    let instance = OakFunctionsInstance::<WasmHandler>::new(
        &initialize_request,
        None, // No observer.
        WasmConfig::default(),
    )
    .context("Failed to create Oak Functions instance")?;

    info!("Executing Wasm claim...");
    let response_bytes =
        instance.handle_user_request(input_bytes).context("Wasm claim execution failed")?;

    // Decode the response byte using the shared wire constants.
    let byte =
        response_bytes.first().ok_or_else(|| anyhow!("Wasm module returned empty response"))?;
    match falsify::Evaluation::from_byte(*byte) {
        Some(falsify::Evaluation::Intact) => {
            info!("Claim intact.");
            Ok(falsify_native::Status::Intact)
        }
        Some(falsify::Evaluation::Falsified) => {
            info!("Claim falsified!");
            Ok(falsify_native::Status::Falsified)
        }
        None => Err(anyhow!("Unexpected evaluation byte from Wasm module: {byte}")),
    }
}
