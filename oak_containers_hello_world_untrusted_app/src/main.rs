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

mod app_client;

use clap::Parser;

const UNTRUSTED_APP_VSOCK_CID: u32 = vsock::VMADDR_CID_HOST;
const UNTRUSTED_APP_VSOCK_PORT: u32 = 8081;

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    let args = oak_containers_launcher::Args::parse();
    let launcher_handle = tokio::task::spawn(oak_containers_launcher::create(args));

    let mut trusted_app_client = app_client::TrustedApplicationClient::create(
        UNTRUSTED_APP_VSOCK_CID,
        UNTRUSTED_APP_VSOCK_PORT,
    )
    .await
    .map_err(|error| anyhow::anyhow!("couldn't create trusted app client: {}", error))?;

    let greeting = trusted_app_client
        .hello("Untrusted App")
        .await
        .map_err(|error| anyhow::anyhow!("couldn't invoke trusted app: {}", error))?;

    println!("Received a greeting from the trusted app: {:?}", greeting);

    launcher_handle.abort();

    Ok(())
}
