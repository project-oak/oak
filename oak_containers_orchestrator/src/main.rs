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

use anyhow::anyhow;
use clap::Parser;
use oak_containers_orchestrator::{IPC_SOCKET_FILE_NAME, UTIL_DIR};
use oak_containers_orchestrator_client::LauncherClient;
use oak_crypto::encryptor::EncryptionKeyProvider;
use oak_remote_attestation::attester::{Attester, EmptyAttestationReportGenerator};
use std::sync::Arc;
use tokio::sync::oneshot::channel;

#[derive(Parser, Debug)]
struct Args {
    #[arg(default_value = "http://10.0.2.100:8080")]
    launcher_addr: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    oak_containers_orchestrator::logging::setup()?;

    let args = Args::parse();

    let launcher_client = Arc::new(
        LauncherClient::create(args.launcher_addr.parse()?)
            .await
            .map_err(|error| anyhow!("couldn't create client: {:?}", error))?,
    );

    let container_bundle = launcher_client
        .get_container_bundle()
        .await
        .map_err(|error| anyhow!("couldn't get container bundle: {:?}", error))?;

    let application_config = launcher_client
        .get_application_config()
        .await
        .map_err(|error| anyhow!("couldn't get application config: {:?}", error))?;

    let attestation_report_generator = Arc::new(EmptyAttestationReportGenerator);
    let encryption_key_provider = Arc::new(EncryptionKeyProvider::new());
    let attester = Attester::new(
        attestation_report_generator,
        encryption_key_provider.clone(),
    );
    let evidence = attester
        .generate_attestation_evidence()
        .map_err(|error| anyhow!("couldn't generate attestation evidence: {:?}", error))?;
    launcher_client
        .send_attestation_evidence(evidence)
        .await
        .map_err(|error| anyhow!("couldn't send attestation evidence: {:?}", error))?;

    let util_dir_absolute_path = std::path::Path::new("/").join(UTIL_DIR);
    tokio::fs::create_dir_all(&util_dir_absolute_path).await?;
    let ipc_path = {
        let mut path = util_dir_absolute_path;
        path.push(IPC_SOCKET_FILE_NAME);
        path
    };
    let (exit_notification_sender, shutdown_receiver) = channel::<()>();

    tokio::try_join!(
        oak_containers_orchestrator::ipc_server::create(
            ipc_path,
            encryption_key_provider,
            attester,
            application_config,
            launcher_client.clone(),
            shutdown_receiver
        ),
        oak_containers_orchestrator::container_runtime::run(
            &container_bundle,
            exit_notification_sender
        ),
        oak_containers_orchestrator::metrics::run(launcher_client),
    )?;

    Ok(())
}
