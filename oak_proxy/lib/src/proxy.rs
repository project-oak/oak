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
                            plaintext_writer.shutdown().await?;
                        } else {
                            log::debug!("[{role}] Peer sent more data.");
                            // let mut session = session.lock().await;
                            session.put_incoming(&data)?;
                            while let Some(plaintext) = session.get_plaintext()? {
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
