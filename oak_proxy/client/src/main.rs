//
// Copyright 2025 The Project Oak Authors
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
//

use std::{net::SocketAddr, sync::Arc};

use clap::Parser;
use oak_proxy_lib::{
    framing::{read_message, write_message},
    proxy::proxy,
};
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ClientSession,
    ProtocolEngine, Session,
};
use tokio::{
    net::{TcpListener, TcpStream},
    sync::Mutex,
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The address on which to listen for incoming connections from the
    /// application (e.g., browser).
    #[arg(long, default_value = "127.0.0.1:9090")]
    listen_address: SocketAddr,

    /// The address of the server proxy.
    #[arg(long, default_value = "127.0.0.1:8081")]
    server_proxy_address: SocketAddr,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let listener = TcpListener::bind(args.listen_address).await?;
    println!("[Client] Listening on {}", args.listen_address);

    loop {
        let (stream, peer_address) = listener.accept().await?;
        println!("[Client] Accepted connection from {}", peer_address);
        let server_proxy_address = args.server_proxy_address;
        tokio::spawn(async move {
            if let Err(err) = handle_connection(stream, server_proxy_address).await {
                eprintln!("[Client] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn handle_connection(
    app_stream: TcpStream,
    server_proxy_address: SocketAddr,
) -> anyhow::Result<()> {
    let mut server_proxy_stream = TcpStream::connect(server_proxy_address).await?;
    println!("[Client] Connected to server proxy at {}", server_proxy_address);

    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let client_session = Arc::new(Mutex::new(ClientSession::create(client_config)?));

    // Handshake
    {
        let mut session = client_session.lock().await;
        while !session.is_open() {
            if let Some(request) = session.get_outgoing_message()? {
                write_message(&mut server_proxy_stream, &request).await?;
            }

            if !session.is_open() {
                let response = read_message(&mut server_proxy_stream).await?;
                session.put_incoming_message(response)?;
            }
        }
    }

    println!("[Client] Oak Session established with server proxy.");

    proxy::<
        ClientSession,
        oak_proto_rust::oak::session::v1::SessionResponse,
        oak_proto_rust::oak::session::v1::SessionRequest,
    >(app_stream, server_proxy_stream, client_session)
    .await
}
