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

use std::net::{Ipv6Addr, SocketAddr};

use anyhow::Context;
use clap::Parser;
use oak_containers_launcher::ChannelType;
use oak_functions_launcher::LookupDataConfig;
use oak_proto_rust::oak::functions::{
    InitializeRequest,
    config::{
        ApplicationConfig, VsockCommunicationChannel, application_config::CommunicationChannel,
    },
};
use prost::Message;
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
    let mut args = Args::parse();

    let lookup_data_config = LookupDataConfig {
        lookup_data_path: args.functions_args.lookup_data,
        // Hard-coded because we are not sure whether we want to configure the update interval.
        update_interval: Some(std::time::Duration::from_secs(60 * 10)),
        // gRPC messages are limited to 4 MiB.
        max_chunk_size: ByteUnit::Mebibyte(4),
    };

    let mut config = ApplicationConfig::default();
    if args.containers_args.communication_channel == ChannelType::VirtioVsock {
        config.communication_channel =
            Some(CommunicationChannel::VsockChannel(VsockCommunicationChannel::default()));

        // If no explicit CID was specified, override it to be the current process ID.
        args.containers_args.qemu_params.virtio_guest_cid.get_or_insert_with(std::process::id);
    }
    args.containers_args.application_config = config.encode_to_vec();

    let mut untrusted_app =
        oak_functions_containers_launcher::UntrustedApp::create(args.containers_args)
            .await
            .context("couldn't create untrusted launcher")?;

    let wasm_bytes = tokio::fs::read(&args.functions_args.wasm)
        .await
        .with_context(|| format!("couldn't read Wasm file {}", args.functions_args.wasm.display()))
        .unwrap();

    let _ = untrusted_app
        .initialize_enclave(InitializeRequest {
            wasm_module: wasm_bytes,
            constant_response_size: args.functions_args.constant_response_size,
        })
        .await
        .map_err(|error| {
            eprintln!("initialize response error: {}", error);
            anyhow::anyhow!("couldn't get encrypted response: {}", error)
        })?;

    let endorsed_evidence = untrusted_app
        .launcher
        .get_endorsed_evidence()
        .await
        .context("couldn't get endorsed evidence")?;
    let evidence =
        endorsed_evidence.evidence.context("endorsed evidence message doesn't contain evidence")?;
    let endorsements = endorsed_evidence
        .endorsements
        .context("endorsed evidence message doesn't contain endorsements")?;

    untrusted_app.setup_lookup_data(lookup_data_config).await?;

    let server_future = oak_functions_containers_launcher::server::new(
        SocketAddr::from((Ipv6Addr::UNSPECIFIED, args.functions_args.port)),
        untrusted_app.oak_functions_client.clone(),
        evidence,
        endorsements,
    );

    // Wait until something dies or we get a signal to terminate.
    tokio::select! {
        _ = tokio::signal::ctrl_c() => {
            log::info!("Ctrl-C received, terminating VMM");
            untrusted_app.launcher.kill().await;
        },
        _ = server_future => {
            log::info!("server terminated, terminating VMM");
            untrusted_app.launcher.kill().await;
        },
        val = untrusted_app.launcher.wait() => {
            log::error!("Unexpected VMM exit, status: {:?}", val);
        },
    }

    Ok(())
}
