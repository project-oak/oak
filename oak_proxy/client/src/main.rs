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
    config::ClientConfig,
    framing::{read_message, write_message},
    proxy::{proxy, PeerRole},
};
use oak_session::{ClientSession, ProtocolEngine, Session};
use tokio::{
    net::{TcpListener, TcpStream},
    sync::Mutex,
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the TOML configuration file.
    #[arg(long, value_parser = crate::config::load_toml::<ClientConfig>)]
    config: ClientConfig,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();

    let Args { config } = Args::parse();

    let listener = TcpListener::bind(config.listen_address).await?;
    log::info!("[Client] Listening on {}", config.listen_address);

    let config = Arc::new(config);
    loop {
        let (stream, peer_address) = listener.accept().await?;
        log::info!("[Client] Accepted connection from {}", peer_address);
        let config = config.clone();
        tokio::spawn(async move {
            if let Err(err) = handle_connection(stream, &config).await {
                log::error!("[Client] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn handle_connection(app_stream: TcpStream, config: &ClientConfig) -> anyhow::Result<()> {
    let mut server_proxy_stream = TcpStream::connect(config.server_proxy_address).await?;
    log::info!("[Client] Connected to server proxy at {}", config.server_proxy_address);

    let client_config = config::build_session_config(
        &config.attestation_generators,
        &config.attestation_verifiers,
    )?;
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

    log::info!("[Client] Oak Session established with server proxy.");

    proxy::<
        ClientSession,
        oak_proto_rust::oak::session::v1::SessionResponse,
        oak_proto_rust::oak::session::v1::SessionRequest,
    >(PeerRole::Client, app_stream, server_proxy_stream, client_session)
    .await
}
