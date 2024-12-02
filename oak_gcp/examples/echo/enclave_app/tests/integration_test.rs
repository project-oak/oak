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

use anyhow::Result;
use tokio::net::TcpListener;

async fn start_server() -> Result<(SocketAddr, tokio::task::JoinHandle<Result<()>>)> {
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await?;
    let addr = listener.local_addr()?;

    Ok((
        addr,
        tokio::spawn(oak_gcp_examples_echo_enclave_app::app_service::create(
            listener,
            Box::new(oak_gcp_examples_echo_enclave_app::app::EchoHandler),
        )),
    ))
}

#[tokio::test]
async fn test_echo() {
    let (addr, _join_handle) = start_server().await.unwrap();

    let url = format!("http://{addr}");

    let mut client = oak_gcp_examples_echo_client::EchoClient::create(url)
        .await
        .expect("couldn't connect to server");

    let decrypted_response =
        client.echo(b"test message").await.expect("couldn't send first request");
    assert_eq!(decrypted_response, b"test message");

    let decrypted_response =
        client.echo(b"another one").await.expect("couldn't send second request");
    assert_eq!(decrypted_response, b"another one");
}
