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

use anyhow::{Context, anyhow};
use oak_proxy_lib::{
    config::ServerConfig,
    proxy::{PeerRole, TlsProxySession, proxy},
    websocket::{read_raw_message, write_raw_message},
};
use oak_session_tls::{OakSessionTlsServerContext, ServerContextConfig};
use tokio::{
    io::AsyncWriteExt,
    net::{TcpListener, TcpStream},
};
use tokio_tungstenite::{MaybeTlsStream, WebSocketStream, accept_async};

pub fn create_tls_context(
    config: &ServerConfig,
) -> anyhow::Result<Arc<OakSessionTlsServerContext>> {
    let cert_path = config
        .tls_cert
        .as_deref()
        .context("tls_cert must be provided when using experimental_tls_session")?;
    let key_path = config
        .tls_key
        .as_deref()
        .context("tls_key must be provided when using experimental_tls_session")?;

    let cert_file = std::fs::File::open(cert_path).context("failed to open cert file")?;
    let key_file = std::fs::File::open(key_path).context("failed to open key file")?;

    let cert_der = oak_session_tls::utils::load_cert_der(std::io::BufReader::new(cert_file));
    let key_der = oak_session_tls::utils::load_key_der(std::io::BufReader::new(key_file));

    let tls_config = ServerContextConfig {
        tls_identity_provider: oak_session_tls::utils::create_static_cert_identity_provider(
            key_der,
            vec![cert_der],
        ),
        client_trust_anchor_provider: None,
        custom_cert_verifier: None,
    };
    Ok(Arc::new(
        OakSessionTlsServerContext::create(tls_config)
            .map_err(|e| anyhow!("failed to create TLS context: {}", e))?,
    ))
}

pub async fn run_loop(listener: TcpListener, config: Arc<ServerConfig>) -> anyhow::Result<()> {
    let tls_context = create_tls_context(&config)?;
    loop {
        let (stream, peer_address) = listener.accept().await?;
        log::info!("[Server] Accepted connection from {}", peer_address);
        let config = config.clone();
        let tls_context = tls_context.clone();
        tokio::spawn(async move {
            let client_stream = match accept_async(MaybeTlsStream::Plain(stream)).await {
                Ok(stream) => stream,
                Err(err) => {
                    log::error!("[Server] Error accepting WebSocket connection: {:?}", err);
                    return;
                }
            };
            if let Err(err) = run_proxy(client_stream, &config, &tls_context).await {
                log::error!("[Server] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn run_proxy(
    client_stream: WebSocketStream<MaybeTlsStream<TcpStream>>,
    config: &ServerConfig,
    tls_context: &OakSessionTlsServerContext,
) -> anyhow::Result<()> {
    let (session, initial_data, client_stream) =
        establish_tls_session(client_stream, tls_context).await?;
    log::info!("[Server] Experimental TLS Session established with client proxy.");

    let backend_address = config.backend_address.context("backend_address wasn't set")?;
    let mut backend_stream = TcpStream::connect(backend_address)
        .await
        .context(format!("error connecting to backend {}", backend_address))?;
    log::info!("[Server] Connected to backend server at {}", backend_address);

    if !initial_data.is_empty() {
        backend_stream.write_all(&initial_data).await?;
    }

    proxy(PeerRole::Server, session, backend_stream, client_stream, config.keep_alive_interval)
        .await
}

async fn establish_tls_session(
    stream: WebSocketStream<MaybeTlsStream<TcpStream>>,
    tls_context: &OakSessionTlsServerContext,
) -> anyhow::Result<(TlsProxySession, Vec<u8>, WebSocketStream<MaybeTlsStream<TcpStream>>)> {
    let stream = Arc::new(tokio::sync::Mutex::new(stream));
    let (session, initial_data) = tls_context
        .new_initialized_session(
            |frame| {
                let stream = stream.clone();
                async move { write_raw_message(&mut *stream.lock().await, frame).await }
            },
            || {
                let stream = stream.clone();
                async move { read_raw_message(&mut *stream.lock().await).await.map(Some) }
            },
        )
        .await
        .map_err(|e| anyhow!("handshake failed: {}", e))?;

    let stream = Arc::try_unwrap(stream).map_err(|_| anyhow!("stream still locked"))?.into_inner();

    Ok((TlsProxySession::new(session), initial_data, stream))
}
