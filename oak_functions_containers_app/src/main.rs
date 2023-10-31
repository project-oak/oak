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
use oak_functions_containers_app::{
    orchestrator_client::OrchestratorClient,
    proto::oak::functions::oak_functions_server::OakFunctionsServer, OakFunctionsContainersService,
};
use oak_remote_attestation::attester::{
    AttestationReportGenerator, EmptyAttestationReportGenerator,
};
use std::{
    net::{IpAddr, Ipv4Addr, SocketAddr},
    sync::Arc,
};
use tokio::net::TcpListener;
use tokio_stream::wrappers::TcpListenerStream;

const OAK_FUNCTIONS_CONTAINERS_APP_PORT: u16 = 8080;

// Starts up and serves an OakFunctionsContainersService instance from the provided TCP listener.
pub async fn serve(
    listener: TcpListener,
    attestation_report_generator: Arc<dyn AttestationReportGenerator>,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(OakFunctionsServer::new(OakFunctionsContainersService::new(
            attestation_report_generator,
        )))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("starting up the service failed with error: {:?}", error))
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = OrchestratorClient::create()
        .await
        .map_err(|error| anyhow!("couldn't create Orchestrator client: {:?}", error))?;
    // To be used when connecting trusted app to orchestrator.
    let _application_config = client.clone().get_application_config().await?;
    let attestation_report_generator = Arc::new(EmptyAttestationReportGenerator);

    let addr = SocketAddr::new(
        IpAddr::V4(Ipv4Addr::UNSPECIFIED),
        OAK_FUNCTIONS_CONTAINERS_APP_PORT,
    );
    let listener = TcpListener::bind(addr).await?;
    let server_handle = tokio::spawn(serve(listener, attestation_report_generator));

    eprintln!("Running Oak Functions on Oak Containers at address: {addr}");
    client.notify_app_ready().await?;
    Ok(server_handle.await??)
}
