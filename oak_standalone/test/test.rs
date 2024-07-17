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

use std::{
    net::{IpAddr, Ipv4Addr, SocketAddr},
    sync::Arc,
};

use anyhow::{Context, Result};
use oak_client::transport::GrpcStreamingTransport;
use oak_grpc::oak::session::v1::streaming_session_client::StreamingSessionClient;
use tokio::net::TcpListener;
use tonic::transport::Channel;

struct TestAdapter {}
impl oak_standalone_service::Adapter for TestAdapter {
    fn invoke(&self, serialized_request: &[u8]) -> anyhow::Result<Vec<u8>> {
        let reversed: Vec<u8> = serialized_request.iter().copied().rev().collect();
        Ok(reversed)
    }
}

async fn start_server() -> Result<(SocketAddr, tokio::task::JoinHandle<Result<()>>)> {
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await?;
    let addr = listener.local_addr()?;

    let adapter = Arc::new(TestAdapter {});

    let (private_encryption_key, public_key) =
        oak_crypto::encryption_key::generate_encryption_key_pair();

    Ok((
        addr,
        tokio::spawn(oak_standalone_service::create(
            listener,
            private_encryption_key,
            public_key,
            adapter,
        )),
    ))
}

#[tokio::test]
async fn test1() {
    // Start server
    let (addr, _join_handle) = start_server().await.unwrap();

    let url = format!("http://{}:{}", addr.ip(), addr.port());

    println!("Connecting to test server on {}", url);

    let channel = Channel::from_shared(url)
        .context("couldn't create gRPC channel")
        .unwrap()
        .connect()
        .await
        .context("couldn't connect via gRPC channel")
        .unwrap();
    let transport = GrpcStreamingTransport::new(StreamingSessionClient::new(channel))
        .await
        .expect("couldn't create GRPC streaming transport");

    // Create client
    let mut oak_client = oak_standalone_client::new(transport).await.unwrap();

    // Send single request, see the response
    assert_eq!(oak_client.invoke(b"abcde").await.unwrap(), b"edcba");
}
