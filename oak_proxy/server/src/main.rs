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
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ProtocolEngine,
    ServerSession, Session,
};
use tokio::{
    net::{TcpListener, TcpStream},
    sync::Mutex,
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The address on which to listen for incoming connections from the client
    /// proxy.
    #[arg(long, default_value = "127.0.0.1:8081")]
    listen_address: SocketAddr,

    /// The address of the backend server to which to forward decrypted traffic.
    #[arg(long, default_value = "127.0.0.1:8080")]
    backend_address: SocketAddr,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let listener = TcpListener::bind(args.listen_address).await?;
    println!("[Server] Listening on {}", args.listen_address);

    loop {
        let (stream, peer_address) = listener.accept().await?;
        println!("[Server] Accepted connection from {}", peer_address);
        let backend_address = args.backend_address;
        tokio::spawn(async move {
            if let Err(err) = handle_connection(stream, backend_address).await {
                eprintln!("[Server] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn handle_connection(
    mut client_stream: TcpStream,
    backend_address: SocketAddr,
) -> anyhow::Result<()> {
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_session = Arc::new(Mutex::new(ServerSession::create(server_config)?));

    // Handshake
    {
        let mut session = server_session.lock().await;
        while !session.is_open() {
            let request = read_message(&mut client_stream).await?;
            session.put_incoming_message(request)?;

            if let Some(response) = session.get_outgoing_message()? {
                write_message(&mut client_stream, &response).await?;
            }
        }
    }

    println!("[Server] Oak Session established with client proxy.");

    let backend_stream = TcpStream::connect(backend_address).await?;
    println!("[Server] Connected to backend server at {}", backend_address);

    proxy::<
        ServerSession,
        oak_proto_rust::oak::session::v1::SessionRequest,
        oak_proto_rust::oak::session::v1::SessionResponse,
    >(backend_stream, client_stream, server_session)
    .await
}
