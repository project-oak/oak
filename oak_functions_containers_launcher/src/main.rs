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

use clap::Parser;
use oak_functions_containers_launcher::proto::oak::functions::InitializeRequest;

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    let args = oak_containers_launcher::Args::parse();
    env_logger::init();

    let mut untrusted_app = oak_functions_containers_launcher::UntrustedApp::create(args)
        .await
        .map_err(|error| anyhow::anyhow!("couldn't create untrusted launcher: {}", error))?;

    let initialize_response = untrusted_app
        .initialize_enclave(InitializeRequest::default())
        .await
        .map_err(|error| anyhow::anyhow!("couldn't get encrypted response: {}", error))?;

    eprintln!(
        "Received an initialization response: {:?}",
        initialize_response
    );

    Ok(())
}
