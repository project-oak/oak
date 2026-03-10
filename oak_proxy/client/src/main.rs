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

use std::{
    net::SocketAddr,
    path::PathBuf,
    sync::Arc,
    time::{SystemTime, UNIX_EPOCH},
};

use anyhow::Context;
use clap::Parser;
use oak_proto_rust::oak::attestation::v1::{CollectedAttestation, collected_attestation};
use oak_proxy_lib::{
    config::{self, ClientConfig},
    proxy::{PeerRole, proxy},
    websocket::{read_message, write_message},
};
use oak_session::{
    ClientSession, ProtocolEngine, Session,
    session::{AttestationEvidence, AttestationPublisher},
};
use prost::Message;
use tokio::net::{TcpListener, TcpStream};
use url::Url;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the TOML configuration file.
    #[arg(long, value_parser = crate::config::load_toml::<ClientConfig>)]
    config: ClientConfig,

    /// The SocketAddr where the proxy should listen (e.g., "127.0.0.1:9090").
    /// This will override the value in the config file.
    #[arg(long, env = "OAK_PROXY_CLIENT_LISTEN_ADDRESS")]
    listen_address: Option<SocketAddr>,

    /// The WebSocket URL of the server proxy.
    /// This will override the value in the config file.
    #[arg(long, env = "OAK_PROXY_SERVER_URL")]
    server_proxy_url: Option<Url>,

    /// File path to write the received attestation evidence to.
    /// This will override the value in the config file.
    #[arg(long, env = "OAK_PROXY_ATTESTATION_OUTPUT_FILE")]
    attestation_output_file: Option<PathBuf>,
}

/// An `AttestationPublisher` that serializes received attestation evidence
/// to a file as a `CollectedAttestation` proto. Writes the evidence
/// regardless of whether verification succeeded or failed.
struct FileAttestationPublisher {
    output_path: PathBuf,
    server_proxy_url: String,
}

impl AttestationPublisher for FileAttestationPublisher {
    fn publish(&self, attestation_evidence: AttestationEvidence) {
        log::info!(
            "[Client] publish() called! evidence_count={}, bindings_count={}, handshake_hash_len={}",
            attestation_evidence.evidence.len(),
            attestation_evidence.evidence_bindings.len(),
            attestation_evidence.handshake_hash.len(),
        );
        let request_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| prost_types::Timestamp {
                seconds: d.as_secs() as i64,
                nanos: d.subsec_nanos() as i32,
            })
            .ok();
        let collected_attestation = CollectedAttestation {
            request_metadata: Some(collected_attestation::RequestMetadata {
                uri: self.server_proxy_url.clone(),
                request_time,
            }),
            endorsed_evidence: attestation_evidence.evidence,
            session_bindings: attestation_evidence.evidence_bindings,
            handshake_hash: attestation_evidence.handshake_hash,
        };

        let encoded = collected_attestation.encode_to_vec();
        log::info!("[Client] Writing {} bytes to '{}'", encoded.len(), self.output_path.display());
        match std::fs::write(&self.output_path, encoded) {
            Ok(()) => {
                log::info!(
                    "[Client] CollectedAttestation written to '{}'",
                    self.output_path.display()
                );
            }
            Err(err) => {
                log::error!(
                    "[Client] Failed to write CollectedAttestation to '{}': {:?}",
                    self.output_path.display(),
                    err
                );
            }
        }
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();

    let Args { mut config, listen_address, server_proxy_url, attestation_output_file } =
        Args::parse();

    // The command-line arguments override the values from the config file.
    if let Some(listen_address) = listen_address {
        config.listen_address = Some(listen_address);
    }
    if let Some(server_proxy_url) = server_proxy_url {
        config.server_proxy_url = Some(server_proxy_url);
    }
    if let Some(attestation_output_file) = attestation_output_file {
        config.attestation_output_file = Some(attestation_output_file);
    }

    let listen_address = config
        .listen_address
        .context("listen_address must be specified in the config file or via an argument")?;
    anyhow::ensure!(config.server_proxy_url.is_some());
    let listener = TcpListener::bind(listen_address).await?;
    log::info!("[Client] Listening on {}", listen_address);

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
    let server_proxy_url =
        config.server_proxy_url.as_ref().context("server_proxy_url wasn't set")?;
    let (mut server_proxy_stream, _) = tokio_tungstenite::connect_async(server_proxy_url).await?;
    log::info!("[Client] Connected to server proxy at {}", server_proxy_url);

    // Create an attestation publisher if an output file is configured.
    let attestation_publisher: Option<Arc<dyn AttestationPublisher>> =
        config.attestation_output_file.as_ref().map(|path| {
            log::info!(
                "[Client] Attestation publisher CREATED, will write to '{}'",
                path.display()
            );
            Arc::new(FileAttestationPublisher {
                output_path: path.clone(),
                server_proxy_url: server_proxy_url.to_string(),
            }) as Arc<dyn AttestationPublisher>
        });

    let client_config = config::build_session_config(
        &config.attestation_generators,
        &config.attestation_verifiers,
        attestation_publisher.as_ref(),
    )?;
    let mut session = ClientSession::create(client_config)?;

    // Handshake
    while !session.is_open() {
        if let Some(request) = session.get_outgoing_message()? {
            write_message(&mut server_proxy_stream, &request).await?;
        }

        if !session.is_open() {
            let response = read_message(&mut server_proxy_stream).await?;
            session.put_incoming_message(response)?;
        }
    }

    log::info!("[Client] Oak Session established with server proxy.");

    proxy::<ClientSession>(
        PeerRole::Client,
        session,
        app_stream,
        server_proxy_stream,
        config.keep_alive_interval,
    )
    .await
}
