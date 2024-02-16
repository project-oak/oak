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

use std::{path::PathBuf, sync::Arc};

use anyhow::{anyhow, Context};
use clap::Parser;
use oak_attestation::attester::{Attester, EmptyAttestationReportGenerator};
use oak_containers_orchestrator::{
    crypto::generate_instance_keys, launcher_client::LauncherClient,
    proto::oak::containers::v1::KeyProvisioningRole,
};
use tokio_util::sync::CancellationToken;

#[global_allocator]
static ALLOCATOR: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

#[derive(Parser, Debug)]
struct Args {
    #[arg(default_value = "http://10.0.2.100:8080")]
    launcher_addr: String,

    #[arg(default_value = "0.0.0.0:4000")]
    orchestrator_addr: String,

    #[arg(long, default_value = "/oak_container")]
    container_dir: PathBuf,

    #[arg(long, default_value = "/oak_utils/orchestrator_ipc")]
    ipc_socket_path: PathBuf,

    #[arg(long, default_value = "oakc")]
    runtime_user: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
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

    let dice_builder = oak_containers_orchestrator::dice::load_stage1_dice_data()?;
    let additional_claims = oak_containers_orchestrator::dice::measure_container_and_config(
        &container_bundle,
        &application_config,
    );
    let (instance_keys, instance_public_keys) = generate_instance_keys();

    let dice_evidence = dice_builder.add_application_keys(
        additional_claims,
        &instance_public_keys.encryption_public_key,
        &instance_public_keys.signing_public_key,
    )?;
    // TODO(#4074): Remove once DICE attestation is fully implemented.
    let attestation_report_generator = Arc::new(EmptyAttestationReportGenerator);
    let attester = Attester::new(
        attestation_report_generator,
        &instance_public_keys.encryption_public_key,
    );
    let evidence = attester
        .generate_attestation_evidence()
        .map_err(|error| anyhow!("couldn't generate attestation evidence: {:?}", error))?;
    launcher_client
        .send_attestation_evidence(evidence, dice_evidence)
        .await
        .map_err(|error| anyhow!("couldn't send attestation evidence: {:?}", error))?;

    if let Some(path) = args.ipc_socket_path.parent() {
        tokio::fs::create_dir_all(path).await?;
    }

    let key_provisioning_role = launcher_client
        .get_key_provisioning_role()
        .await
        .map_err(|error| anyhow!("couldn't get key provisioning role: {:?}", error))?;
    let group_keys = Arc::new(match key_provisioning_role {
        KeyProvisioningRole::Unspecified => anyhow::bail!("unspecified key provisioning role"),
        KeyProvisioningRole::Leader => {
            // TODO(#4442): Sign group public keys in the enclave evidence.
            let (group_keys, _) = instance_keys.generate_group_keys();
            group_keys
        }
        KeyProvisioningRole::Dependant => {
            let get_group_keys_response = launcher_client
                .get_group_keys()
                .await
                .map_err(|error| anyhow!("couldn't get group keys: {:?}", error))?;
            instance_keys
                .provide_group_keys(get_group_keys_response)
                .context("couldn't provide group keys")?
        }
    });

    let _metrics = oak_containers_orchestrator::metrics::run(launcher_client.clone())?;

    let user = nix::unistd::User::from_name(&args.runtime_user)
        .context(format!("error resolving user {}", args.runtime_user))?
        .context(format!("user `{}` not found", args.runtime_user))?;

    let cancellation_token = CancellationToken::new();
    tokio::try_join!(
        oak_containers_orchestrator::ipc_server::create(
            &args.ipc_socket_path,
            instance_keys,
            group_keys.clone(),
            application_config,
            launcher_client,
            cancellation_token.clone(),
        ),
        oak_containers_orchestrator::key_provisioning::create(
            &args.orchestrator_addr,
            group_keys,
            cancellation_token.clone(),
        ),
        oak_containers_orchestrator::container_runtime::run(
            &container_bundle,
            &args.container_dir,
            user.uid,
            user.gid,
            &args.ipc_socket_path,
            cancellation_token,
        ),
    )?;

    Ok(())
}
