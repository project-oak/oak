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
use futures::channel::mpsc;
use oak_hello_world_proto::oak::containers::example::enclave_application_client::EnclaveApplicationClient;
use oak_session::{
    Session,
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
};
use tokio::net::TcpListener;
use tonic::transport::Channel;

const APPLICATION_CONFIG: &[u8] = b"fake_config";

async fn start_server() -> Result<(SocketAddr, tokio::task::JoinHandle<Result<()>>)> {
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await?;
    let addr = listener.local_addr()?;

    Ok((
        addr,
        tokio::spawn(oak_containers_examples_hello_world_enclave_app::app_service::create(
            listener,
            oak_containers_examples_hello_world_enclave_app::app::HelloWorldApplicationHandler {
                application_config: APPLICATION_CONFIG.to_vec(),
            },
        )),
    ))
}

#[tokio::test]
async fn test_noise() {
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

    let mut client = EnclaveApplicationClient::new(channel);

    let (mut tx, rx) = mpsc::channel(10);

    let mut response_stream =
        client.oak_session(rx).await.expect("couldn't send stream request").into_inner();

    // We don't have a noise client impl yet, so we need to manage the session
    // manually.
    let mut client_session = oak_session::ClientSession::create(
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
    )
    .expect("could not create client session");

    while !client_session.is_open() {
        let request = client_session.next_init_message().expect("expected client init message");
        tx.try_send(request).expect("failed to send to server");
        if !client_session.is_open() {
            let response = response_stream
                .message()
                .await
                .expect("expected a response")
                .expect("response was failure");
            client_session.handle_init_message(response).expect("failed to handle init response");
        }
    }

    let request = client_session.encrypt(b"standalone user").expect("failed to send request");
    tx.try_send(request).expect("failed to send request");

    let result = response_stream
        .message()
        .await
        .expect("no response ready")
        .expect("failed to get response");
    let result = client_session.decrypt(result).expect("failed to decrypt result");
    let app_config_len = APPLICATION_CONFIG.len();
    assert_eq!(
        String::from_utf8(result).unwrap(),
        format!(
            "Hello from the enclave, standalone user! Btw, the app has a config with a length of {app_config_len} bytes."
        ),
    );
}
