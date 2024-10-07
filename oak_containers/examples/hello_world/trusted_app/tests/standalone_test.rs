//
// Copyright 2024 The Project Oak Authors
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

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use anyhow::{Context, Result};
use oak_client::{client::OakClient, verifier::InsecureAttestationVerifier};
use oak_client_tonic::transport::GrpcStreamingTransport;
use oak_containers_sdk::{
    standalone::StandaloneOrchestrator, OakSessionContext, OrchestratorInterface,
};
use oak_hello_world_proto::oak::containers::example::trusted_application_client::TrustedApplicationClient;
use tokio::net::TcpListener;
use tonic::transport::Channel;

async fn start_server() -> Result<(SocketAddr, tokio::task::JoinHandle<Result<()>>)> {
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await?;
    let addr = listener.local_addr()?;

    let mut orchestrator = StandaloneOrchestrator::default();
    let encryption_key_handle = orchestrator.get_instance_encryption_key_handle();

    let endorsed_evidence = orchestrator.get_endorsed_evidence().await?;
    let application_config = orchestrator.get_application_config().await?;

    Ok((
        addr,
        tokio::spawn(oak_containers_hello_world_trusted_app::app_service::create(
            listener,
            OakSessionContext::new(
                Box::new(encryption_key_handle),
                endorsed_evidence,
                Box::new(
                    oak_containers_hello_world_trusted_app::app::HelloWorldApplicationHandler {
                        application_config,
                    },
                ),
            ),
        )),
    ))
}

#[tokio::test]
async fn test1() {
    // Start server
    let (addr, _join_handle) = start_server().await.unwrap();

    let url = format!("http://{addr}");

    println!("Connecting to test server on {}", url);

    let channel = Channel::from_shared(url)
        .context("couldn't create gRPC channel")
        .unwrap()
        .connect()
        .await
        .context("couldn't connect via gRPC channel")
        .unwrap();

    let mut client = TrustedApplicationClient::new(channel);

    let transport = GrpcStreamingTransport::new(|rx| client.session(rx))
        .await
        .expect("couldn't create GRPC streaming transport");

    let attestation_verifier = InsecureAttestationVerifier {};

    // Create client
    let mut oak_client = OakClient::create(transport, &attestation_verifier).await.unwrap();

    // Send single request, see the response
    assert_eq!(
        String::from_utf8(oak_client.invoke(b"standalone user").await.unwrap()).unwrap(),
        "Hello from the trusted side, standalone user! Btw, the Trusted App has a config with a length of 4 bytes."
    );
}
