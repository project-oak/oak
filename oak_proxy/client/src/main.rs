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

mod noise;
mod tls;

use std::{
    net::SocketAddr,
    path::PathBuf,
    sync::Arc,
    time::{SystemTime, UNIX_EPOCH},
};

use anyhow::Context;
use clap::Parser;
use oak_proto_rust::oak::attestation::v1::{CollectedAttestation, collected_attestation};
use oak_proxy_lib::config::ClientConfig;
use oak_session::session::{AttestationEvidence, AttestationPublisher};
use prost::Message;
use tokio::{
    io::AsyncWriteExt,
    net::{TcpListener, TcpStream},
};
use url::Url;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the TOML configuration file.
    #[arg(long, value_parser = oak_proxy_lib::config::load_toml::<ClientConfig>)]
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
pub(crate) struct FileAttestationPublisher {
    pub(crate) output_path: PathBuf,
    pub(crate) server_proxy_url: String,
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

impl Args {
    fn get_config(mut self) -> anyhow::Result<ClientConfig> {
        // The command-line arguments override the values from the config file.
        if let Some(listen_address) = self.listen_address {
            self.config.listen_address = Some(listen_address);
        }
        if self.server_proxy_url.is_some() {
            self.config.server_proxy_url = self.server_proxy_url.clone();
        }
        if let Some(attestation_output_file) = self.attestation_output_file {
            self.config.attestation_output_file = Some(attestation_output_file);
        }

        self.config
            .listen_address
            .as_ref()
            .context("listen_address must be specified in the config file or via an argument")?;
        self.config
            .server_proxy_url
            .as_ref()
            .context("server_proxy_url must be specified in the config file or via an argument")?;

        Ok(self.config)
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();

    let config = Arc::new(Args::parse().get_config()?);

    let listen_address = config.listen_address.unwrap();
    let listener = TcpListener::bind(listen_address).await?;
    log::info!("[Client] Listening on {}", listen_address);

    if config.experimental_tls_session {
        tls::run_loop(listener, config).await
    } else {
        noise::run_loop(listener, config).await
    }
}

pub(crate) async fn write_http_502(
    mut app_stream: TcpStream,
    err: &anyhow::Error,
) -> anyhow::Error {
    let error_msg = format!("Attestation/Handshake Failed: {:#}", err);
    let body = format!("[Oak-Proxy] {}\n", error_msg);
    let response = format!(
        "HTTP/1.1 502 Bad Gateway\r\nContent-Type: text/plain\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
        body.len(),
        body
    );
    if let Err(write_err) = app_stream.write_all(response.as_bytes()).await {
        log::warn!("Failed to write HTTP 502 error response: {:?}", write_err);
    }
    let _ = app_stream.flush().await;
    let _ = app_stream.shutdown().await;
    anyhow::anyhow!("Handshake/attestation failed (sent HTTP 502 to client): {:#}", err)
}
