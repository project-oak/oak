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

use anyhow::Context;
use oak_proxy_lib::{
    config::{self, ServerConfig},
    proxy::{NoiseProxySession, PeerRole, proxy},
    websocket::{read_message, write_message},
};
use oak_session::{ProtocolEngine, ServerSession, Session};
use tokio::net::{TcpListener, TcpStream};
use tokio_tungstenite::{MaybeTlsStream, WebSocketStream, accept_async};

pub async fn run_loop(listener: TcpListener, config: Arc<ServerConfig>) -> anyhow::Result<()> {
    loop {
        let (stream, peer_address) = listener.accept().await?;
        log::info!("[Server] Accepted connection from {}", peer_address);
        let config = config.clone();
        tokio::spawn(async move {
            let client_stream = match accept_async(MaybeTlsStream::Plain(stream)).await {
                Ok(stream) => stream,
                Err(err) => {
                    log::error!("[Server] Error accepting WebSocket connection: {:?}", err);
                    return;
                }
            };
            if let Err(err) = run_proxy(client_stream, &config).await {
                log::error!("[Server] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn run_proxy(
    client_stream: WebSocketStream<MaybeTlsStream<TcpStream>>,
    config: &ServerConfig,
) -> anyhow::Result<()> {
    let (session, client_stream) = establish_noise_session(client_stream, config).await?;
    log::info!("[Server] Oak Session established with client proxy.");

    let backend_address = config.backend_address.context("backend_address wasn't set")?;
    let backend_stream = TcpStream::connect(backend_address)
        .await
        .context(format!("error connecting to backend {}", backend_address))?;
    log::info!("[Server] Connected to backend server at {}", backend_address);

    proxy(PeerRole::Server, session, backend_stream, client_stream, config.keep_alive_interval)
        .await
}

async fn establish_noise_session(
    mut stream: WebSocketStream<MaybeTlsStream<TcpStream>>,
    config: &ServerConfig,
) -> anyhow::Result<(NoiseProxySession<ServerSession>, WebSocketStream<MaybeTlsStream<TcpStream>>)>
{
    let server_config = config::build_session_config(
        &config.attestation_generators,
        &config.attestation_verifiers,
        None,
    )?;
    let mut session = ServerSession::create(server_config)?;

    while !session.is_open() {
        let request = read_message(&mut stream).await?;
        session.put_incoming_message(request)?;

        if let Some(response) = session.get_outgoing_message()? {
            write_message(&mut stream, &response).await?;
        }
    }

    Ok((NoiseProxySession::new(session), stream))
}
