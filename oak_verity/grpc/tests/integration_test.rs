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

//! Integration test for the Oak Verity GCP service.

use std::{collections::BTreeMap, time::Duration};

use anyhow::Result;
use oak_grpc::oak::verity::{
    oak_verity_service_client::OakVerityServiceClient,
    oak_verity_service_server::OakVerityServiceServer,
};
use oak_proto_rust::oak::verity::{ExecuteRequest, ExecutionManifest};
use prost::Message;
use tonic::transport::{Channel, Endpoint, Server};

const ECHO_WASM_PATH: &str = "oak_functions/examples/echo/echo.wasm";

async fn create_client(port: u16) -> Result<OakVerityServiceClient<Channel>> {
    // Let's give the server some time to start.
    tokio::time::sleep(Duration::from_secs(2)).await;

    let endpoint = Endpoint::from_shared(format!("http://[::1]:{}", port))?;
    let channel = endpoint.connect().await?;
    Ok(OakVerityServiceClient::new(channel))
}

async fn run_server(port: u16) -> anyhow::Result<()> {
    let service = oak_verity_grpc::OakVerityService::new(BTreeMap::new());
    let addr = format!("[::]:{}", port).parse::<std::net::SocketAddr>()?;
    Server::builder().add_service(OakVerityServiceServer::new(service)).serve(addr).await?;
    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
async fn test_execute_with_echo_wasm() -> Result<()> {
    println!("Current dir: {:?}", std::env::current_dir());
    let port = portpicker::pick_unused_port().expect("failed to pick a port");
    let server_handle = tokio::spawn(run_server(port));

    // The server is automatically started as part of the test setup.
    let mut client = create_client(port).await?;

    let wasm_path = oak_file_utils::data_path(ECHO_WASM_PATH);
    let wasm_module = std::fs::read(&wasm_path)
        .unwrap_or_else(|_| panic!("Failed to read echo.wasm from {}", wasm_path.display()));
    let test_input = b"Hello, from a test!".to_vec();

    let request = ExecuteRequest { wasm_module, input_data: test_input.clone() };

    let response = client.execute(request).await?.into_inner();

    // Verify the echo functionality.
    assert_eq!(response.output_data, test_input, "Output must match input for echo Wasm");

    // Verify the manifest.
    let manifest = ExecutionManifest::decode(response.serialized_manifest.as_slice())?;
    assert!(manifest.input_data_digest.is_some(), "Input digest must be present");
    assert!(manifest.wasm_module_digest.is_some(), "Wasm digest must be present");
    assert!(manifest.output_data_digest.is_some(), "Output digest must be present");

    let input_digest = manifest.input_data_digest.unwrap().sha2_256;
    let output_digest = manifest.output_data_digest.unwrap().sha2_256;

    assert_eq!(input_digest, output_digest, "Input and output digests must match for echo");

    // No assertion generators are configured, so the assertions map must be
    // empty.
    assert!(response.assertions.is_empty());

    server_handle.abort();
    Ok(())
}
