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

//! Integration test that launches the trusted app and invokes it.

use std::{
    env,
    net::{IpAddr, Ipv4Addr, SocketAddr},
    sync::Once,
};

use oak_client::{
    client::OakClient, proto::oak::session::v1::streaming_session_client::StreamingSessionClient,
    transport::GrpcStreamingTransport, verifier::InsecureAttestationVerifier,
};
use oak_containers_launcher::Args;
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
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    let args = Args { container_bundle, ..Args::default_for_root(env!("WORKSPACE_ROOT")) };

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await.expect("couldn't bind listener");
    let addr = listener.local_addr().expect("couldn't get server addr");

    tokio::spawn(oak_containers_hello_world_untrusted_app::service::create(listener, args));

    let url = format!("http://{}:{}", addr.ip(), addr.port());

    println!("Connecting to test server on {}", url);

    let channel = Channel::from_shared(url)
        .expect("couldn't create gRPC channel")
        .connect()
        .await
        .expect("couldn't connect via gRPC channel");
    let transport = GrpcStreamingTransport::new(StreamingSessionClient::new(channel))
        .await
        .expect("Couldn't create streaming transport");

    let verifier = InsecureAttestationVerifier {};
    let mut client = OakClient::create(transport, &verifier).await.expect("Couldn't create client");

    let result = client.invoke(b"end to end test xyzzy").await.expect("Invoke failed");
    assert_eq!(result, b"Hello from the trusted side, end to end test xyzzy! Btw, the Trusted App has a config with a length of 0 bytes.")
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn hello_world() {
    run_hello_world_test(Args::default_for_root(env!("WORKSPACE_ROOT")).container_bundle).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cc_hello_world() {
    run_hello_world_test(
        format!(
            "{}bazel-bin/cc/containers/hello_world_trusted_app/bundle.tar",
            env!("WORKSPACE_ROOT")
        )
        .into(),
    )
    .await;
}
