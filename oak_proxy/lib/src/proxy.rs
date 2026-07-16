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

use std::{collections::VecDeque, fmt, time::Duration};

use bytes::Bytes;
use futures::{SinkExt, StreamExt};
use oak_proto_rust::oak::session::v1::PlaintextMessage;
use oak_session::{ProtocolEngine, Session};
use oak_session_tls::OakSessionTls;
use prost::Message;
use rand::Rng;
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::TcpStream,
};
use tokio_tungstenite::{MaybeTlsStream, WebSocketStream, tungstenite};

pub enum PeerRole {
    Client,
    Server,
}

impl fmt::Display for PeerRole {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PeerRole::Client => write!(f, "Client"),
            PeerRole::Server => write!(f, "Server"),
        }
    }
}

/// A trait that abstracts the session-specific logic for the proxy loop.
pub trait ProxySession: Send + 'static {
    /// Ingests data received from the remote peer.
    fn put_incoming(&mut self, data: &[u8]) -> anyhow::Result<()>;
    /// Retrieves decrypted plaintext meant for the local application.
    fn get_plaintext(&mut self) -> anyhow::Result<Option<Vec<u8>>>;
    /// Ingests plaintext received from the local application.
    fn put_plaintext(&mut self, data: &[u8]) -> anyhow::Result<()>;
    /// Retrieves encrypted data (frames) meant for the remote peer.
    fn get_outgoing(&mut self) -> anyhow::Result<Option<Vec<u8>>>;
    /// Returns the base64url-encoded JSON string representing the session's
    /// attestation feedback header payload.
    fn attestation_header_payload(&self) -> Option<String> {
        None
    }
}

impl<P: ProxySession + ?Sized> ProxySession for Box<P> {
    fn put_incoming(&mut self, data: &[u8]) -> anyhow::Result<()> {
        (**self).put_incoming(data)
    }

    fn get_plaintext(&mut self) -> anyhow::Result<Option<Vec<u8>>> {
        (**self).get_plaintext()
    }

    fn put_plaintext(&mut self, data: &[u8]) -> anyhow::Result<()> {
        (**self).put_plaintext(data)
    }

    fn get_outgoing(&mut self) -> anyhow::Result<Option<Vec<u8>>> {
        (**self).get_outgoing()
    }

    fn attestation_header_payload(&self) -> Option<String> {
        (**self).attestation_header_payload()
    }
}

/// A ProxySession implementation for standard Noise-based Oak Sessions.
pub struct NoiseProxySession<S> {
    session: S,
}

impl<S> NoiseProxySession<S>
where
    S: ProtocolEngine + Session + Send + 'static,
    S::Input: Message + Default + Send + 'static,
    S::Output: Message + Default + Send + 'static,
{
    pub fn new(session: S) -> Self {
        Self { session }
    }
}

impl<S> ProxySession for NoiseProxySession<S>
where
    S: ProtocolEngine + Session + Send + 'static,
    S::Input: Message + Default + Send + 'static,
    S::Output: Message + Default + Send + 'static,
{
    fn put_incoming(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let message = S::Input::decode(data)?;
        self.session.put_incoming_message(message)?;
        Ok(())
    }

    fn get_plaintext(&mut self) -> anyhow::Result<Option<Vec<u8>>> {
        Ok(self.session.read()?.map(|m| m.plaintext))
    }

    fn put_plaintext(&mut self, data: &[u8]) -> anyhow::Result<()> {
        self.session.write(PlaintextMessage { plaintext: data.to_vec() })?;
        Ok(())
    }

    fn get_outgoing(&mut self) -> anyhow::Result<Option<Vec<u8>>> {
        Ok(self.session.get_outgoing_message()?.map(|m| m.encode_to_vec()))
    }

    fn attestation_header_payload(&self) -> Option<String> {
        use base64::Engine;
        use oak_attestation_verification::decode_event_proto;
        use oak_proto_rust::oak::attestation::v1::{
            ConfidentialSpaceAssertion, ConfidentialSpaceEndorsement, SessionBindingPublicKeyData,
        };
        use prost::Message;

        let evidence = self.session.get_peer_attestation_evidence().ok()?;
        if evidence.evidence.is_empty() && evidence.assertions.is_empty() {
            return None;
        }
        let handshake_handle = hex::encode(&evidence.handshake_hash);

        let mut jwt_string = None;
        for assertion in evidence.assertions.values() {
            if let Ok(cs_assertion) =
                ConfidentialSpaceAssertion::decode(assertion.content.as_slice())
                && let Ok(jwt) = String::from_utf8(cs_assertion.jwt_token.clone())
            {
                jwt_string = Some(jwt);
                break;
            }
        }
        if jwt_string.is_none() {
            for endorsed_evidence in evidence.evidence.values() {
                if let Some(endorsements) = &endorsed_evidence.endorsements {
                    for event in &endorsements.events {
                        if let Ok(cs_endorsement) = ConfidentialSpaceEndorsement::try_from(event) {
                            jwt_string = Some(cs_endorsement.jwt_token.clone());
                            break;
                        }
                    }
                }
                if jwt_string.is_some() {
                    break;
                }
            }
        }

        let mut custom_artifacts = std::collections::BTreeMap::new();
        let mut root_layer = None;
        let mut workload_layer = None;
        if let Some(jwt) = jwt_string {
            let parts: Vec<&str> = jwt.split('.').collect();
            if parts.len() >= 2 {
                let payload_b64 = parts[1];
                if let Ok(decoded_bytes) =
                    base64::engine::general_purpose::URL_SAFE_NO_PAD.decode(payload_b64.as_bytes())
                    && let Ok(claims) =
                        serde_json::from_slice::<oak_attestation_gcp::jwt::Claims>(&decoded_bytes)
                {
                    root_layer = Some(crate::http::RootLayerFeedback {
                        platform: "AMD_SEV_SNP".to_string(),
                        allow_debug: claims.debug_status != "disabled-since-boot",
                        ..Default::default()
                    });
                    workload_layer = Some(crate::http::WorkloadLayerFeedback {
                        workload_type: "OAK_CONTAINERS".to_string(),
                        container_image_digest: Some(claims.submods.container.image_digest.clone()),
                        ..Default::default()
                    });

                    custom_artifacts
                        .insert("gcp_software_name".to_string(), claims.software_name.clone());
                    if let Some(hw) = claims.hardware_model.as_ref() {
                        custom_artifacts.insert("gcp_hardware_model".to_string(), hw.clone());
                    }
                    if let Some(gce) = claims.submods.gce.as_ref() {
                        if !gce.project_id.is_empty() {
                            custom_artifacts
                                .insert("gcp_project_id".to_string(), gce.project_id.clone());
                        }
                        if !gce.instance_name.is_empty() {
                            custom_artifacts
                                .insert("gcp_instance_name".to_string(), gce.instance_name.clone());
                        }
                        if !gce.zone.is_empty() {
                            custom_artifacts.insert("gcp_zone".to_string(), gce.zone.clone());
                        }
                    }
                    if !claims.submods.container.image_reference.is_empty() {
                        custom_artifacts.insert(
                            "gcp_container_image_reference".to_string(),
                            claims.submods.container.image_reference.clone(),
                        );
                    }
                }
            }
        }

        let mut session_keys = None;
        for endorsed_evidence in evidence.evidence.values() {
            if let Some(evidence_inner) = &endorsed_evidence.evidence
                && let Some(event_log) = &evidence_inner.event_log
            {
                for encoded_event in &event_log.encoded_events {
                    if let Ok(key_data) = decode_event_proto::<SessionBindingPublicKeyData>(
                        "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData",
                        encoded_event,
                    ) {
                        session_keys = Some(crate::http::VerifiedSessionKeys {
                            session_binding_public_key: format!(
                                "hex:{}",
                                hex::encode(key_data.session_binding_public_key)
                            ),
                            ..Default::default()
                        });
                        break;
                    }
                }
            }
            if session_keys.is_some() {
                break;
            }
        }

        let feedback = crate::http::OakAttestationFeedback {
            status: "verified".to_string(),
            handshake_handle,
            verification_time: humantime_serde::re::humantime::format_rfc3339_seconds(
                std::time::SystemTime::now(),
            )
            .to_string(),
            root_layer: root_layer.unwrap_or_default(),
            workload_layer: workload_layer.unwrap_or_default(),
            session_keys: session_keys.unwrap_or_default(),
            custom_artifacts,
            ..Default::default()
        };
        let json = serde_json::to_string(&feedback).ok()?;
        Some(base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(json.as_bytes()))
    }
}

/// A ProxySession implementation for TLS-based Oak Sessions.
pub struct TlsProxySession {
    session: OakSessionTls,
    plaintext_buffer: VecDeque<Vec<u8>>,
    outgoing_buffer: VecDeque<Vec<u8>>,
}

impl TlsProxySession {
    pub fn new(session: OakSessionTls) -> Self {
        Self { session, plaintext_buffer: VecDeque::new(), outgoing_buffer: VecDeque::new() }
    }
}

impl ProxySession for TlsProxySession {
    fn put_incoming(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let plaintext = self.session.decrypt(data)?;
        if !plaintext.is_empty() {
            self.plaintext_buffer.push_back(plaintext);
        }
        Ok(())
    }

    fn get_plaintext(&mut self) -> anyhow::Result<Option<Vec<u8>>> {
        Ok(self.plaintext_buffer.pop_front())
    }

    fn put_plaintext(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let encrypted = self.session.encrypt(data)?;
        if !encrypted.is_empty() {
            self.outgoing_buffer.push_back(encrypted);
        }
        Ok(())
    }

    fn get_outgoing(&mut self) -> anyhow::Result<Option<Vec<u8>>> {
        Ok(self.outgoing_buffer.pop_front())
    }
}

/// Manages a bidirectional proxy between a local stream and a remote stream.
///
/// - `plaintext_stream`: The stream connected to the local application or
///   backend.
/// - `encrypted_stream`: The stream connected to the remote proxy.
/// - `session`: The `ProxySession` instance.
pub async fn proxy<S: ProxySession>(
    role: PeerRole,
    mut session: S,
    plaintext_stream: TcpStream,
    encrypted_stream: WebSocketStream<MaybeTlsStream<TcpStream>>,
    keep_alive_interval: Duration,
    mode: crate::config::ProxyMode,
) -> anyhow::Result<()> {
    let (mut plaintext_reader, mut plaintext_writer) = tokio::io::split(plaintext_stream);
    let (mut encrypted_writer, mut encrypted_reader) = encrypted_stream.split();

    let mut plaintext_buffer = vec![0; 1024];

    // Stores whether we are in the middle of a ping
    let mut ping_queue: VecDeque<Bytes> = VecDeque::new();
    // The interval between pings, and also the timeout for their corresponding pong
    let mut keep_alive = tokio::time::interval(keep_alive_interval);
    // The first tick is immediate, so we consume it before starting the loop.
    keep_alive.tick().await;

    let mut application_done = false;
    let mut peer_done = false;

    // Cache computed attestation header for the session (M1).
    let cached_attestation_header = if mode == crate::config::ProxyMode::Http {
        session.attestation_header_payload()
    } else {
        None
    };
    // Reassembly buffer for HTTP headers split across TLS chunks (H2).
    let mut http_header_buf = Vec::new();

    loop {
        if application_done && peer_done {
            encrypted_writer.send(tungstenite::Message::Close(None)).await?;
            break;
        }

        tokio::select! {
            Some(res) = encrypted_reader.next() => {
                match res? {
                    tungstenite::Message::Binary(data) => {
                        anyhow::ensure!(!peer_done, "Peer was only mostly half-closed");
                        if data.is_empty() {
                            peer_done = true;
                            log::debug!("[{role}] Peer half-closed, shutting down plaintext writer.");
                            if !http_header_buf.is_empty() {
                                plaintext_writer.write_all(&http_header_buf).await?;
                                http_header_buf.clear();
                            }
                            plaintext_writer.shutdown().await?;
                        } else {
                            log::debug!("[{role}] Peer sent more data.");
                            // let mut session = session.lock().await;
                            session.put_incoming(&data)?;
                            while let Some(plaintext) = session.get_plaintext()? {
                                if let Some(header_val) = &cached_attestation_header {
                                    if http_header_buf.is_empty() && !crate::http::is_http_start(&plaintext) {
                                        plaintext_writer.write_all(&plaintext).await?;
                                        continue;
                                    }
                                    http_header_buf.extend_from_slice(&plaintext);
                                    if let Some(spliced) = crate::http::splice_attestation_header(&http_header_buf, header_val) {
                                        plaintext_writer.write_all(&spliced).await?;
                                        http_header_buf.clear();
                                    } else if http_header_buf.len() > 65536 {
                                        plaintext_writer.write_all(&http_header_buf).await?;
                                        http_header_buf.clear();
                                    }
                                    continue;
                                }
                                plaintext_writer.write_all(&plaintext).await?;
                            }
                        }
                    }
                    tungstenite::Message::Ping(ping_data) => {
                        log::debug!("[{role}] Peer sent ping message {}", hex::encode(&ping_data));
                        encrypted_writer.send(tungstenite::Message::Pong(ping_data)).await?;
                    }
                    tungstenite::Message::Pong(pong_data) => {
                        match ping_queue.pop_back() {
                            Some(ping_data) if ping_data == pong_data => {
                                log::debug!("[{role}] Peer sent pong message {}", hex::encode(pong_data));
                            }
                            _ => {
                                anyhow::bail!("[{role}] Peer sent unexpected pong: {}", hex::encode(pong_data));
                            }
                        }
                    }
                    _ => anyhow::bail!("Peer sent unsupported message type"),
                }
            }
            Ok(n) = plaintext_reader.read(&mut plaintext_buffer), if !application_done => {
                if n == 0 {
                    log::debug!("[{role}] Application closed, sending half-close.");
                    application_done = true;
                    encrypted_writer.send(tungstenite::Message::Binary(Bytes::new())).await?;
                } else {
                    log::debug!("[{role}] Application sent {n} more bytes.");
                    session.put_plaintext(&plaintext_buffer[..n])?;
                    while let Some(encrypted) = session.get_outgoing()? {
                        encrypted_writer.send(tungstenite::Message::Binary(encrypted.into())).await?;
                    }
                }
            }
            _ = keep_alive.tick() => {
                if !ping_queue.is_empty() {
                    anyhow::bail!("[{role}] The peer did not sent a pong for previous ping on time");
                }

                // Send a randomly generated ping
                let mut payload = vec![0u8; 8];
                rand::rng().fill(&mut payload[..]);
                log::debug!("[{role}] Ding, dong! It's pinging time! Sending ping {}", hex::encode(&payload));
                ping_queue.push_front(payload.clone().into());
                encrypted_writer.send(tungstenite::Message::Ping(payload.into())).await?;
            }
        }
    }

    log::debug!("[{role}] Proxy stream ended.");

    Ok(())
}
