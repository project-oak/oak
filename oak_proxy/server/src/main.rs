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

use std::sync::Arc;

use clap::Parser;
use oak_proxy_lib::{
    config,
    config::ServerConfig,
    proxy::{proxy, PeerRole},
    websocket::{read_message, write_message},
};
use oak_session::{ProtocolEngine, ServerSession, Session};
use tokio::net::{TcpListener, TcpStream};
use tokio_tungstenite::{accept_async, MaybeTlsStream};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the TOML configuration file.
    #[arg(long, value_parser = crate::config::load_toml::<ServerConfig>)]
    config: ServerConfig,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();

    let Args { config } = Args::parse();

    let listener = TcpListener::bind(config.listen_address).await?;
    log::info!("[Server] Listening on {}", config.listen_address);

    let config = Arc::new(config);
    loop {
        let (stream, peer_address) = listener.accept().await?;
        log::info!("[Server] Accepted connection from {}", peer_address);
        let config = config.clone();
        tokio::spawn(async move {
            if let Err(err) = handle_connection(stream, &config).await {
                log::error!("[Server] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn handle_connection(client_stream: TcpStream, config: &ServerConfig) -> anyhow::Result<()> {
    let mut client_stream = accept_async(MaybeTlsStream::Plain(client_stream)).await?;
    let server_config = config::build_session_config(
        &config.attestation_generators,
        &config.attestation_verifiers,
    )?;
    let mut session = ServerSession::create(server_config)?;

    // Handshake
    {
        //let mut session = server_session.lock().await;
        while !session.is_open() {
            let request = read_message(&mut client_stream).await?;
            session.put_incoming_message(request)?;

            if let Some(response) = session.get_outgoing_message()? {
                write_message(&mut client_stream, &response).await?;
            }
        }
    }

    log::info!("[Server] Oak Session established with client proxy.");

    let backend_stream = TcpStream::connect(config.backend_address).await?;
    log::info!("[Server] Connected to backend server at {}", config.backend_address);

    proxy::<
        ServerSession,
        oak_proto_rust::oak::session::v1::SessionRequest,
        oak_proto_rust::oak::session::v1::SessionResponse,
    >(PeerRole::Server, session, backend_stream, client_stream, config.keep_alive_interval)
    .await
}
