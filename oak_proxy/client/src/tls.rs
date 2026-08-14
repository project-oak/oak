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
    config::ClientConfig,
    proxy::{PeerRole, TlsProxySession, proxy},
    websocket::{read_raw_message, write_raw_message},
};
use oak_session_tls::{ClientContextConfig, OakSessionTlsClientContext};
use tokio::net::{TcpListener, TcpStream};
use tokio_tungstenite::{MaybeTlsStream, WebSocketStream};

pub fn create_tls_context(
    config: &ClientConfig,
) -> anyhow::Result<Arc<OakSessionTlsClientContext>> {
    let ca_path = config
        .tls_ca
        .as_deref()
        .context("tls_ca must be provided when using experimental_tls_session")?;
    let ca_file = std::fs::File::open(ca_path).context("failed to open CA certificate file")?;
    let ca_der = oak_session_tls::utils::load_cert_der(std::io::BufReader::new(ca_file));

    let tls_config = ClientContextConfig {
        server_trust_anchor_provider: Some(
            oak_session_tls::utils::create_static_trust_anchor_provider(ca_der),
        ),
        tls_identity_provider: None,
        custom_cert_verifier: None,
        expected_server_name: None,
    };
    Ok(Arc::new(
        OakSessionTlsClientContext::create(tls_config)
            .map_err(|e| anyhow!("failed to create TLS context: {}", e))?,
    ))
}

pub async fn run_loop(listener: TcpListener, config: Arc<ClientConfig>) -> anyhow::Result<()> {
    let tls_context = create_tls_context(&config)?;
    loop {
        let (stream, peer_address) = listener.accept().await?;
        log::info!("[Client] Accepted connection from {}", peer_address);
        let config = config.clone();
        let tls_context = tls_context.clone();
        tokio::spawn(async move {
            if let Err(err) = run_proxy(stream, &config, &tls_context).await {
                log::error!("[Client] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn run_proxy(
    app_stream: TcpStream,
    config: &ClientConfig,
    tls_context: &OakSessionTlsClientContext,
) -> anyhow::Result<()> {
    let setup_result = async {
        let server_proxy_url =
            config.server_proxy_url.as_ref().context("server_proxy_url wasn't set")?;
        let (server_proxy_stream, _) = tokio_tungstenite::connect_async(server_proxy_url).await?;
        log::info!("[Client] Connected to server proxy at {}", server_proxy_url);

        let (session, stream) = establish_tls_session(server_proxy_stream, tls_context).await?;
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

async fn establish_tls_session(
    stream: WebSocketStream<MaybeTlsStream<TcpStream>>,
    tls_context: &OakSessionTlsClientContext,
) -> anyhow::Result<(TlsProxySession, WebSocketStream<MaybeTlsStream<TcpStream>>)> {
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

    anyhow::ensure!(initial_data.is_empty(), "Unexpected initial data after TLS handshake");

    log::info!("[Client] Experimental TLS Session established with server proxy.");
    Ok((TlsProxySession::new(session), stream))
}
