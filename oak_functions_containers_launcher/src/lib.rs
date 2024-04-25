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

pub mod proto {
    pub mod oak {
        pub mod functions {
            tonic::include_proto!("oak.functions");
            pub mod config {
                tonic::include_proto!("oak.functions.config");
            }
        }
        pub use oak_proto_rust::oak::{attestation, crypto};
    }
}

mod lookup;
pub mod server;

use anyhow::Context;
use oak_containers_launcher::{Launcher, TrustedApplicationAddress};
use oak_functions_launcher::LookupDataConfig;
use tokio::time::Duration;
use tokio_vsock::VsockStream;
use tonic::transport::Endpoint;
use tower::service_fn;

use crate::proto::oak::functions::{
    oak_functions_client::OakFunctionsClient as GrpcOakFunctionsClient, InitializeRequest,
    InitializeResponse,
};

pub struct UntrustedApp {
    pub oak_functions_client: GrpcOakFunctionsClient<tonic::transport::channel::Channel>,
    pub launcher: Launcher,
}

impl UntrustedApp {
    pub async fn create(launcher_args: oak_containers_launcher::Args) -> anyhow::Result<Self> {
        let mut launcher = oak_containers_launcher::Launcher::create(launcher_args).await?;

        let oak_functions_client: GrpcOakFunctionsClient<tonic::transport::channel::Channel> = {
            let channel = match launcher.get_trusted_app_address().await? {
                TrustedApplicationAddress::Network(trusted_app_address) => {
                    Endpoint::from_shared(format!("http://{trusted_app_address}"))
                        .context("couldn't form channel")?
                        .connect_timeout(Duration::from_secs(120))
                        .connect()
                        .await
                        .context("couldn't connect to trusted app")?
                }
                TrustedApplicationAddress::VirtioVsock(trusted_app_address) => {
                    // The common URI scheme would be `vsock:cid:port` (see
                    // https://grpc.github.io/grpc/cpp/md_doc_naming.html), but this is not palatable
                    // to the URI class in Rust. The URL is ignored anyway as we're going to
                    // override the connector so it doesn't matter what we pass in there.
                    Endpoint::from_shared(format!(
                        "vsock://{}:{}",
                        trusted_app_address.cid(),
                        trusted_app_address.port()
                    ))
                    .context("couldn't form channel")?
                    .connect_timeout(Duration::from_secs(120))
                    .connect_with_connector(service_fn(move |_| {
                        VsockStream::connect(trusted_app_address)
                    }))
                    .await
                    .context("couldn't connect to trusted app")?
                }
            };
            GrpcOakFunctionsClient::new(channel)
        };

        Ok(Self { launcher, oak_functions_client })
    }

    pub async fn initialize_enclave(
        &mut self,
        initialize_request: InitializeRequest,
    ) -> Result<InitializeResponse, Box<dyn std::error::Error>> {
        let initialize_response = self
            .oak_functions_client
            .initialize(initialize_request)
            .await
            .context("couldn't send initialize request")?
            .into_inner();
        Ok(initialize_response)
    }

    pub async fn kill(&mut self) {
        self.launcher.kill().await;
    }

    pub async fn setup_lookup_data(&mut self, config: LookupDataConfig) -> anyhow::Result<()> {
        log::info!("setting up lookup data");
        update_lookup_data(&mut self.oak_functions_client, &config).await?;

        // Spawn task to periodically refresh lookup data.
        if config.update_interval.is_some() {
            tokio::spawn(setup_periodic_update(self.oak_functions_client.clone(), config));
        }
        Ok(())
    }
}

async fn setup_periodic_update(
    mut client: GrpcOakFunctionsClient<tonic::transport::channel::Channel>,
    config: LookupDataConfig,
) {
    // Only set periodic update if an interval is given.
    let mut interval =
        tokio::time::interval(config.update_interval.expect("No update interval given."));
    loop {
        // Wait before updating because we just loaded the lookup data.
        interval.tick().await;
        let _ = update_lookup_data(&mut client, &config).await;
        // Ignore errors in updates of lookup data after the initial update.
    }
}

async fn update_lookup_data(
    client: &mut GrpcOakFunctionsClient<tonic::transport::channel::Channel>,
    config: &LookupDataConfig,
) -> anyhow::Result<()> {
    log::info!("updating lookup data");
    let start = std::time::Instant::now();
    let result =
        lookup::update_lookup_data(client, &config.lookup_data_path, config.max_chunk_size).await;
    log::info!("updated lookup data in {}ms", start.elapsed().as_millis());
    result
}
