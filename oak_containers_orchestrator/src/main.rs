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

mod logging;

use anyhow::anyhow;
use clap::Parser;
use oak_containers_orchestrator_client::LauncherClient;

#[derive(Parser, Debug)]
struct Args {
    #[arg(long, default_value_t = 2)]
    launcher_vsock_cid: u32,

    #[arg(long, default_value_t = 8080)]
    launcher_vsock_port: u32,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let _ = logging::setup()?;

    let args = Args::parse();

    let mut launcher_client =
        LauncherClient::create(args.launcher_vsock_cid, args.launcher_vsock_port)
            .await
            .map_err(|error| anyhow!("couldn't create client: {:?}", error))?;

    let container_bundle = launcher_client
        .get_container_bundle()
        .await
        .map_err(|error| anyhow!("couldn't get container bundle: {:?}", error))?;

    let _application_config = launcher_client
        .get_application_config()
        .await
        .map_err(|error| anyhow!("couldn't get application config: {:?}", error))?;

    Ok(())
}
