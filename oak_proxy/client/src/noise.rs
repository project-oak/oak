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
    config::{self, ClientConfig},
    proxy::{NoiseProxySession, PeerRole, proxy},
    websocket::{read_message, write_message},
};
use oak_session::{ClientSession, ProtocolEngine, Session, session::AttestationPublisher};
use tokio::net::{TcpListener, TcpStream};
use tokio_tungstenite::{MaybeTlsStream, WebSocketStream};

pub async fn run_loop(listener: TcpListener, config: Arc<ClientConfig>) -> anyhow::Result<()> {
    loop {
        let (stream, peer_address) = listener.accept().await?;
        log::info!("[Client] Accepted connection from {}", peer_address);
        let config = config.clone();
        tokio::spawn(async move {
            if let Err(err) = run_proxy(stream, &config).await {
                log::error!("[Client] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn run_proxy(app_stream: TcpStream, config: &ClientConfig) -> anyhow::Result<()> {
    let setup_result = async {
        let server_proxy_url =
            config.server_proxy_url.as_ref().context("server_proxy_url wasn't set")?;
        let (server_proxy_stream, _) = tokio_tungstenite::connect_async(server_proxy_url).await?;
        log::info!("[Client] Connected to server proxy at {}", server_proxy_url);

        // Create an attestation publisher if an output file is configured.
        let attestation_publisher: Option<Arc<dyn AttestationPublisher>> =
            config.attestation_output_file.as_ref().map(|path| {
                log::info!(
                    "[Client] Attestation publisher CREATED, will write to '{}'",
                    path.display()
                );
                Arc::new(crate::FileAttestationPublisher {
                    output_path: path.clone(),
                    server_proxy_url: server_proxy_url.to_string(),
                }) as Arc<dyn AttestationPublisher>
            });

        let (session, stream) =
            establish_noise_session(server_proxy_stream, config, attestation_publisher.as_ref())
                .await?;
        Ok((session, stream))
    }
    .await;

    match setup_result {
        Ok((session, stream)) => {
            proxy(PeerRole::Client, session, app_stream, stream, config.keep_alive_interval).await
        }
        Err(err) => Err(crate::write_http_502(app_stream, &err).await),
    }
}

async fn establish_noise_session(
    mut stream: WebSocketStream<MaybeTlsStream<TcpStream>>,
    config: &ClientConfig,
    attestation_publisher: Option<&Arc<dyn AttestationPublisher>>,
) -> anyhow::Result<(NoiseProxySession<ClientSession>, WebSocketStream<MaybeTlsStream<TcpStream>>)>
{
    let client_config = config::build_session_config(
        &config.attestation_generators,
        &config.attestation_verifiers,
        attestation_publisher,
    )?;
    let mut session = ClientSession::create(client_config)?;

    while !session.is_open() {
        if let Some(request) = session.get_outgoing_message()? {
            write_message(&mut stream, &request).await?;
        }

        if !session.is_open() {
            let response = read_message(&mut stream).await?;
            session.put_incoming_message(response)?;
        }
    }

    log::info!("[Client] Oak Session established with server proxy.");
    Ok((NoiseProxySession::new(session), stream))
}
