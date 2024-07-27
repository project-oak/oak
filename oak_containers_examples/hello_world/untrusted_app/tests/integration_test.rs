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
    path::PathBuf,
    sync::Once,
};

use oak_client::{
    client::OakClient,
    transport::{EvidenceProvider, GrpcStreamingTransport, Transport},
    verifier::InsecureAttestationVerifier,
};
use oak_containers_hello_world_untrusted_app::demo_transport::{self, DemoTransport};
use oak_containers_launcher::Args;
use oak_grpc::oak::session::v1::streaming_session_client::StreamingSessionClient;
use tokio::net::TcpListener;
use tonic::transport::Channel;

static INIT_LOGGING: Once = Once::new();

fn init_logging() {
    INIT_LOGGING.call_once(|| {
        env_logger::init();
    });
}

trait TransportCreator<T: Transport + EvidenceProvider> {
    async fn create(listener: TcpListener, args: Args) -> T;
}

async fn run_hello_world_test<TC: TransportCreator<T>, T: Transport + EvidenceProvider>(
    container_bundle: std::path::PathBuf,
) {
    init_logging();
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    let args = Args { container_bundle, ..Args::default_for_root(env!("WORKSPACE_ROOT")) };

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await.expect("couldn't bind listener");

    let transport = TC::create(listener, args).await;

    let verifier = InsecureAttestationVerifier {};
    let mut client = OakClient::create(transport, &verifier).await.expect("Couldn't create client");

    let result = client.invoke(b"end to end test xyzzy").await.expect("Invoke failed");
    assert_eq!(result, b"Hello from the trusted side, end to end test xyzzy! Btw, the Trusted App has a config with a length of 0 bytes.")
}

struct GrpcStreamingTransportCreator {}

impl TransportCreator<GrpcStreamingTransport> for GrpcStreamingTransportCreator {
    async fn create(listener: TcpListener, args: Args) -> GrpcStreamingTransport {
        let addr = listener.local_addr().expect("couldn't get server addr");
        tokio::spawn(oak_containers_hello_world_untrusted_app::service::create(listener, args));
        let url = format!("http://{}:{}", addr.ip(), addr.port());
        println!("Connecting to test gRPC server on {}", url);
        let channel = Channel::from_shared(url.to_string())
            .expect("couldn't create gRPC channel")
            .connect()
            .await
            .expect("couldn't connect via gRPC channel");

        let mut client = StreamingSessionClient::new(channel);

        GrpcStreamingTransport::new(|rx| client.stream(rx))
            .await
            .expect("couldn't create GRPC streaming transport")
    }
}

struct DemoTransportCreator {}

impl TransportCreator<DemoTransport> for DemoTransportCreator {
    async fn create(listener: TcpListener, args: Args) -> DemoTransport {
        let addr = listener.local_addr().expect("couldn't get server addr");
        tokio::spawn(oak_containers_hello_world_untrusted_app::http_service::serve(listener, args));
        let url = format!("http://{}:{}", addr.ip(), addr.port());
        println!("Connecting to test REST server on {}", url);
        demo_transport::DemoTransport::new(url)
    }
}

fn rust_hello_world_bundle() -> PathBuf {
    Args::default_for_root(env!("WORKSPACE_ROOT")).container_bundle
}

fn cc_hello_world_bundle() -> PathBuf {
    format!("{}bazel-bin/cc/containers/hello_world_trusted_app/bundle.tar", env!("WORKSPACE_ROOT"))
        .into()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn hello_world_grpc_streaming() {
    run_hello_world_test::<GrpcStreamingTransportCreator, _>(rust_hello_world_bundle()).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn hello_world_http_post() {
    run_hello_world_test::<DemoTransportCreator, _>(rust_hello_world_bundle()).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cc_hello_world_grpc_streaming() {
    run_hello_world_test::<GrpcStreamingTransportCreator, _>(cc_hello_world_bundle()).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cc_hello_world_http_post() {
    run_hello_world_test::<DemoTransportCreator, _>(cc_hello_world_bundle()).await;
}
