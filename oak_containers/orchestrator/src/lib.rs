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
use launcher_client::LauncherClient;
#[allow(deprecated)]
use oak_attestation::ApplicationKeysAttester;
use oak_attestation_types::{attester::Attester, util::Serializable};
use oak_containers_agent::metrics::MetricsConfig;
use oak_containers_attestation::generate_instance_keys;
use oak_proto_rust::oak::containers::v1::KeyProvisioningRole;
use prost::Message;
use tokio_util::sync::CancellationToken;
use tonic::transport::Uri;

mod cdi;
pub mod container_runtime;
pub mod dice;
pub mod ipc_server;
pub mod key_provisioning;
pub mod launcher_client;
pub mod logging;

#[derive(Parser, Debug)]
struct Args {
    #[arg(env, default_value = "http://10.0.2.100:8080")]
    launcher_addr: Uri,

    #[arg(default_value = "10.0.2.15:4000")]
    orchestrator_addr: String,

    #[arg(long, default_value = "/oak_container")]
    container_dir: PathBuf,

    #[arg(long, default_value = "/oak_utils/orchestrator_ipc")]
    ipc_socket_path: PathBuf,

    #[arg(long, default_value = "oakc")]
    runtime_user: String,
}

#[allow(deprecated)]
pub async fn main<A: Attester + ApplicationKeysAttester + Serializable + 'static>(
) -> anyhow::Result<()> {
    std::env::set_var("RUST_BACKTRACE", "1");
    crate::logging::setup()?;

    let args = Args::parse();

    let launcher_client = Arc::new(
        LauncherClient::create(args.launcher_addr.clone())
            .await
            .map_err(|error| anyhow!("couldn't create client: {:?}", error))?,
    );

    let metrics_config = MetricsConfig {
        launcher_addr: args.launcher_addr.to_string(),
        scope: "orchestrator",
        excluded_metrics: None,
    };

    let _oak_observer = oak_containers_agent::metrics::init_metrics(metrics_config);

    // Get key provisioning role.
    let key_provisioning_role = launcher_client
        .get_key_provisioning_role()
        .await
        .map_err(|error| anyhow!("couldn't get key provisioning role: {:?}", error))?;

    // Generate application keys.
    let (instance_keys, instance_public_keys) = generate_instance_keys();
    #[cfg(feature = "application_keys")]
    let (mut group_keys, group_public_keys) =
        if key_provisioning_role == KeyProvisioningRole::Leader {
            let (group_keys, group_public_keys) = instance_keys.generate_group_keys();
            (Some(Arc::new(group_keys)), Some(group_public_keys))
        } else {
            (None, None)
        };
    #[cfg(not(feature = "application_keys"))]
    let (mut group_keys, _group_public_keys) =
        if key_provisioning_role == KeyProvisioningRole::Leader {
            let (group_keys, group_public_keys) = instance_keys.generate_group_keys();
            (Some(Arc::new(group_keys)), Some(group_public_keys))
        } else {
            (None, None)
        };

    // Load application.
    let container_bundle = launcher_client
        .get_container_bundle()
        .await
        .map_err(|error| anyhow!("couldn't get container bundle: {:?}", error))?;
    let application_config = launcher_client
        .get_application_config()
        .await
        .map_err(|error| anyhow!("couldn't get application config: {:?}", error))?;

    // Create a container event and add it to the event log.
    let mut attester: A = crate::dice::load_stage1_dice_data()?;
    let container_event = oak_containers_attestation::create_container_event(
        container_bundle.clone(),
        &application_config[..],
        &instance_public_keys,
    );
    let encoded_event = container_event.encode_to_vec();
    // Spawn the `extend`` operation on a separate thread to support cases where we
    // have async attesters.
    let attester = tokio::runtime::Handle::current()
        .spawn_blocking(move || {
            attester
                .extend(&encoded_event)
                .context("couldn't add container event to the evidence")?;
            Ok::<A, anyhow::Error>(attester)
        })
        .await??;

    // Add the container event to the DICE chain.
    let evidence = {
        #[cfg(feature = "application_keys")]
        {
            // Spawn the `quote` operation on a separate thread to support cases where we
            // have async attesters.
            tokio::runtime::Handle::current()
                .spawn_blocking(move || {
                    let container_layer =
                        oak_containers_attestation::create_container_dice_layer(&container_event);
                    attester.add_application_keys(
                        container_layer,
                        &instance_public_keys.encryption_public_key,
                        &instance_public_keys.signing_public_key,
                        if let Some(ref group_public_keys) = group_public_keys {
                            Some(&group_public_keys.encryption_public_key)
                        } else {
                            None
                        },
                        None,
                    )
                })
                .await??
        }
        #[cfg(not(feature = "application_keys"))]
        {
            // Spawn the `quote` operation on a separate thread to support cases where we
            // have async attesters.
            tokio::runtime::Handle::current().spawn_blocking(move || attester.quote()).await??
        }
    };
    // Send the attestation evidence to the Hostlib.
    launcher_client
        .send_attestation_evidence(evidence.clone())
        .await
        .map_err(|error| anyhow!("couldn't send attestation evidence: {:?}", error))?;

    // Request group keys.
    if key_provisioning_role == KeyProvisioningRole::Follower {
        let get_group_keys_response = launcher_client
            .get_group_keys()
            .await
            .map_err(|error| anyhow!("couldn't get group keys: {:?}", error))?;
        let provisioned_group_keys = instance_keys
            .provide_group_keys(get_group_keys_response)
            .context("couldn't provide group keys")?;
        group_keys = Some(Arc::new(provisioned_group_keys));
    }

    if let Some(path) = args.ipc_socket_path.parent() {
        tokio::fs::create_dir_all(path).await?;
    }

    let endorsements = launcher_client
        .get_endorsements()
        .await
        .map_err(|e| anyhow!("coudln't get endorsements from launcher: {e:?}"))?;

    let (orchestrator_server, crypto_server) = crate::ipc_server::create_services(
        evidence,
        endorsements,
        instance_keys,
        group_keys.clone().context("group keys were not provisioned")?,
        application_config,
        launcher_client,
    );

    // Start application and gRPC servers.
    let user = nix::unistd::User::from_name(&args.runtime_user)
        .context(format!("error resolving user {}", args.runtime_user))?
        .context(format!("user `{}` not found", args.runtime_user))?;
    let cancellation_token = CancellationToken::new();
    tokio::try_join!(
        crate::ipc_server::server(
            &args.ipc_socket_path,
            orchestrator_server,
            crypto_server,
            cancellation_token.clone(),
        ),
        crate::key_provisioning::create(
            &args.orchestrator_addr,
            group_keys.context("group keys were not provisioned")?,
            cancellation_token.clone(),
        ),
        crate::container_runtime::run(
            container_bundle,
            &args.container_dir,
            user.uid,
            user.gid,
            &args.ipc_socket_path,
            cancellation_token,
        ),
    )?;

    Ok(())
}
