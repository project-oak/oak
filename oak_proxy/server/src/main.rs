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

use std::{fs, sync::Arc};

use clap::Parser;
use oak_proxy_lib::{
    config,
    config::ServerConfig,
    framing::{read_message, write_message},
    proxy::{proxy, PeerRole},
};
use oak_session::{ProtocolEngine, ServerSession, Session};
use tokio::{
    net::{TcpListener, TcpStream},
    sync::Mutex,
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the TOML configuration file.
    #[arg(long)]
    config: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let config_str = fs::read_to_string(args.config)?;
    let config: ServerConfig = toml::from_str(&config_str)?;

    let listener = TcpListener::bind(config.listen_address).await?;
    println!("[Server] Listening on {}", config.listen_address);

    let config = Arc::new(config);
    loop {
        let (stream, peer_address) = listener.accept().await?;
        println!("[Server] Accepted connection from {}", peer_address);
        let config = config.clone();
        tokio::spawn(async move {
            if let Err(err) = handle_connection(stream, &config).await {
                eprintln!("[Server] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn handle_connection(
    mut client_stream: TcpStream,
    config: &ServerConfig,
) -> anyhow::Result<()> {
    let server_config = config::build_session_config(
        &config.attestation_generators,
        &config.attestation_verifiers,
    )?;
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

    let backend_stream = TcpStream::connect(config.backend_address).await?;
    println!("[Server] Connected to backend server at {}", config.backend_address);

    proxy::<
        ServerSession,
        oak_proto_rust::oak::session::v1::SessionRequest,
        oak_proto_rust::oak::session::v1::SessionResponse,
    >(PeerRole::Server, backend_stream, client_stream, server_session)
    .await
}
