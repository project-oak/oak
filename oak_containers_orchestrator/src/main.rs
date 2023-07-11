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

mod container_runtime;
mod ipc_server;
mod logging;

use anyhow::anyhow;
use clap::Parser;
use oak_containers_orchestrator_client::{
    proto::oak::session::v1::AttestationEvidence, LauncherClient,
};

// Utility directory that is shared between the orchestrator & container
const UTIL_DIR: &str = "oak_utils";
const IPC_SOCKET_FILE_NAME: &str = "orchestrator_ipc";

#[derive(Parser, Debug)]
struct Args {
    #[arg(default_value = "http://10.0.2.2:8080")]
    launcher_addr: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    logging::setup()?;

    let args = Args::parse();

    let mut launcher_client = LauncherClient::create(args.launcher_addr.parse()?)
        .await
        .map_err(|error| anyhow!("couldn't create client: {:?}", error))?;

    let container_bundle = launcher_client
        .get_container_bundle()
        .await
        .map_err(|error| anyhow!("couldn't get container bundle: {:?}", error))?;

    let application_config = launcher_client
        .get_application_config()
        .await
        .map_err(|error| anyhow!("couldn't get application config: {:?}", error))?;

    let evidence = AttestationEvidence {
        encryption_public_key: vec![],
        signing_public_key: vec![],
        attestation: vec![],
        signed_application_data: vec![],
    };
    launcher_client
        .send_attestation_evidence(evidence)
        .await
        .map_err(|error| anyhow!("couldn't send attestation evidence: {:?}", error))?;

    let util_dir_absolute_path = std::path::Path::new("/").join(crate::UTIL_DIR);
    tokio::fs::create_dir_all(&util_dir_absolute_path).await?;
    let ipc_path = {
        let mut path = util_dir_absolute_path;
        path.push(IPC_SOCKET_FILE_NAME);
        path
    };

    tokio::try_join!(
        crate::ipc_server::create(ipc_path, application_config),
        container_runtime::run(&container_bundle)
    )?;

    Ok(())
}
