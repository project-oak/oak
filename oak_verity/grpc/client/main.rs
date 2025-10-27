//
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
//

//! A gRPC client that calls out to an Oak Verity service.

use std::{
    convert::Infallible,
    fs,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result};
use clap::Parser;
use oak_grpc::oak::verity::oak_verity_service_client::OakVerityServiceClient;
use oak_proto_rust::oak::verity::ExecuteRequest;
use prost::Message;

#[derive(Parser, Debug)]
#[command(name = "oak_verity_grpc_client", about = "gRPC client for Oak Verity")]
struct Flags {
    /// Server address.
    #[arg(long, value_name = "ADDRESS")]
    server_address: String,

    /// Path to the input data file.
    #[arg(long, value_parser = path_parser, value_name = "FILE")]
    input_data: PathBuf,

    /// Path to the WebAssembly module file.
    #[arg(long, value_parser = path_parser, value_name = "FILE")]
    wasm_module: PathBuf,

    /// Optional: Path where the raw output data will be written.
    #[arg(long, value_parser = path_parser, value_name = "FILE")]
    output_data: Option<PathBuf>,

    /// Optional: Path where the full ExecuteResponse protobuf will be written
    /// (contains both output data and manifest).
    #[arg(long, value_parser = path_parser, value_name = "FILE")]
    output_response: Option<PathBuf>,
}

fn path_parser(arg_value: &str) -> Result<PathBuf, Infallible> {
    // https://bazel.build/docs/user-manual#running-executables
    Ok(Path::new(&std::env::var("BUILD_WORKING_DIRECTORY").unwrap_or_default()).join(arg_value))
}

#[tokio::main]
async fn main() -> Result<()> {
    let flags = Flags::parse();

    // Support relative paths by resolving against BUILD_WORKING_DIRECTORY
    // This allows the CLI to work correctly when invoked via `bazel run`.
    let base_path = std::env::var("BUILD_WORKING_DIRECTORY").unwrap_or_default();
    let base_path = Path::new(&base_path);

    // Read the input data that will be passed to the Wasm module.
    let input_path = base_path.join(&flags.input_data);
    let input_data = fs::read(&input_path)
        .with_context(|| format!("Failed to read input data from {:?}", input_path))?;

    // Read the compiled Wasm module (must be Oak Functions compatible).
    let wasm_path = base_path.join(&flags.wasm_module);
    let wasm_module = fs::read(&wasm_path)
        .with_context(|| format!("Failed to read Wasm module from {:?}", wasm_path))?;

    // Create the execution request with input data and Wasm module.
    let request = ExecuteRequest { input_data, wasm_module };

    let mut client = OakVerityServiceClient::connect(flags.server_address).await?;
    let response = client.execute(request).await?.into_inner();

    println!("✅ Execution successful!");

    // Optionally write the raw output data to a file.
    if let Some(output_data_path) = flags.output_data {
        let output_data_path = base_path.join(output_data_path);
        fs::write(&output_data_path, &response.output_data)
            .with_context(|| format!("Failed to write output data to {:?}", output_data_path))?;
        println!("   Raw output data written to: {:?}", output_data_path);
    }

    // Optionally write the full ExecuteResponse protobuf (contains both output_data
    // and manifest).
    if let Some(output_response_path) = flags.output_response {
        let response_bytes = response.encode_to_vec();

        let output_response_path = base_path.join(output_response_path);
        fs::write(&output_response_path, &response_bytes).with_context(|| {
            format!("Failed to write ExecuteResponse to {:?}", output_response_path)
        })?;
        println!("   ExecuteResponse protobuf written to: {:?}", output_response_path);
        println!(
            "   (includes output data + manifest with digests for input, Wasm module, and output)"
        );
    }

    Ok(())
}
