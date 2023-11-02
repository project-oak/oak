//
// Copyright 2023 The Project Oak Authors
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

use anyhow::Context;
use clap::Parser;
use oak_functions_containers_launcher::proto::oak::functions::InitializeRequest;
use oak_functions_launcher::LookupDataConfig;
use ubyte::ByteUnit;

#[derive(Parser, Debug)]
struct Args {
    #[clap(flatten)]
    containers_args: oak_containers_launcher::Args,

    #[clap(flatten)]
    functions_args: oak_functions_launcher::Args,
}

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    env_logger::init();
    let args = Args::parse();

    let lookup_data_config = LookupDataConfig {
        lookup_data_path: args.functions_args.lookup_data,
        // Hard-coded because we are not sure whether we want to configure the update interval.
        update_interval: Some(std::time::Duration::from_secs(60 * 10)),
        // Fix the maximum size of a chunk to the proto limit size of 2 GiB.
        max_chunk_size: ByteUnit::Gibibyte(2),
    };

    let mut untrusted_app =
        oak_functions_containers_launcher::UntrustedApp::create(args.containers_args)
            .await
            .map_err(|error| anyhow::anyhow!("couldn't create untrusted launcher: {}", error))?;

    let wasm_bytes = tokio::fs::read(&args.functions_args.wasm)
        .await
        .with_context(|| {
            format!(
                "couldn't read Wasm file {}",
                args.functions_args.wasm.display()
            )
        })
        .unwrap();

    let initialize_response = untrusted_app
        .initialize_enclave(InitializeRequest {
            wasm_module: wasm_bytes,
            constant_response_size: args.functions_args.constant_response_size,
        })
        .await
        .map_err(|error| {
            eprintln!("initialize response error: {}", error);
            anyhow::anyhow!("couldn't get encrypted response: {}", error)
        })?;

    let public_key_info = initialize_response
        .public_key_info
        .as_ref()
        .expect("no public key info returned");
    log::info!(
        "obtained public key ({} bytes)",
        public_key_info.public_key.len()
    );

    untrusted_app.setup_lookup_data(lookup_data_config).await?;

    log::info!(
        "Received an initialization response: {:?}",
        initialize_response
    );

    Ok(())
}
