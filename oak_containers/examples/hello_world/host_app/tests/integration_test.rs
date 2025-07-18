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

//! Integration test that launches the enclave app and invokes it.

use std::{
    net::{IpAddr, Ipv4Addr, SocketAddr},
    path::PathBuf,
    sync::Once,
    time::Duration,
};

use futures::StreamExt;
use oak_containers_examples_hello_world_host_app::launcher_args::launcher_args;
use oak_hello_world_proto::oak::containers::example::host_application_client::HostApplicationClient;
use oak_session::{
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    session::{ClientSession, Session},
};
use tokio::net::TcpListener;
use tonic::transport::Channel;

static INIT_LOGGING: Once = Once::new();

fn init_logging() {
    INIT_LOGGING.call_once(|| {
        env_logger::init();
    });
}

async fn run_hello_world_test(container_bundle: std::path::PathBuf) {
    init_logging();
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    assert!(container_bundle.exists(), "Couldn't find container bundle at {container_bundle:?}");
    let args = launcher_args(container_bundle).expect("failed to create launcher args");

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await.expect("couldn't bind listener");
    let addr = listener.local_addr().expect("couldn't get server addr");

    tokio::spawn(oak_containers_examples_hello_world_host_app::service::create(listener, args));

    let url = format!("http://{}:{}", addr.ip(), addr.port());

    println!("Connecting to test server on {}", url);

    let channel = Channel::from_shared(url.to_string())
        .expect("couldn't create gRPC channel")
        .connect()
        .await
        .expect("couldn't connect via gRPC channel");

    let mut client = HostApplicationClient::new(channel);

    let (mut tx, rx) = futures::channel::mpsc::channel(10);
    let mut response_stream =
        client.oak_session(rx).await.expect("failed to start stream").into_inner();

    let mut client_session = ClientSession::create(
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
    )
    .expect("failed to create client session");

    while !client_session.is_open() {
        let request = client_session.next_init_message().expect("expected client init message");
        tx.try_send(request).expect("failed to send to server");
        if !client_session.is_open() {
            let response = response_stream
                .next()
                .await
                .expect("expected a response")
                .expect("response was failure");
            client_session.handle_init_message(response).expect("failed to handle init response");
        }
    }

    let request = client_session.encrypt(b"end to end test xyzzy").expect("failed to send request");
    tx.try_send(request).expect("failed to send request");

    let result =
        response_stream.next().await.expect("no response ready").expect("failed to get response");
    let result = client_session.decrypt(result).expect("failed to decrypt result");

    // Sleep a bit to let logs come through, helps for debugging failures.
    tokio::time::sleep(Duration::from_secs(5)).await;
    assert_eq!(result, b"Hello from the enclave, end to end test xyzzy! Btw, the app has a config with a length of 0 bytes.")
}

fn rust_hello_world_bundle() -> PathBuf {
    oak_file_utils::data_path("oak_containers/examples/hello_world/enclave_app/bundle.tar")
}

fn cc_hello_world_bundle() -> PathBuf {
    oak_file_utils::data_path("cc/containers/hello_world_enclave_app/bundle.tar")
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn hello_world_grpc_streaming() {
    run_hello_world_test(rust_hello_world_bundle()).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cc_hello_world_grpc_streaming() {
    run_hello_world_test(cc_hello_world_bundle()).await;
}
