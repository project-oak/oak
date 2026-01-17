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
use oak_session::{ProtocolEngine, Session};
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

/// Manages a bidirectional proxy between a local stream and a remote stream.
///
/// - `plaintext_stream`: The stream connected to the local application or
///   backend.
/// - `encrypted_stream`: The stream connected to the remote proxy.
/// - `session`: The `oak_session` instance.
pub async fn proxy<S>(
    role: PeerRole,
    mut session: S,
    plaintext_stream: TcpStream,
    encrypted_stream: WebSocketStream<MaybeTlsStream<TcpStream>>,
    keep_alive_interval: Duration,
) -> anyhow::Result<()>
where
    S: ProtocolEngine + Session + Send + 'static,
    S::Input: prost::Message + Default,
    S::Output: prost::Message,
{
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
                            let message = S::Input::decode(data)?;
                            session.put_incoming_message(message)?;
                            if let Some(plaintext) = session.read()? {
                                plaintext_writer.write_all(&plaintext.plaintext).await?;
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
                    //let mut session = session.lock().await;
                    log::debug!("[{role}] Application sent {n} more bytes.");
                    session.write(oak_proto_rust::oak::session::v1::PlaintextMessage {
                        plaintext: plaintext_buffer[..n].to_vec(),
                    })?;
                    if let Some(encrypted) = session.get_outgoing_message()? {
                        encrypted_writer.send(tungstenite::Message::Binary(encrypted.encode_to_vec().into())).await?;
                    }
                }
            }
            _ = keep_alive.tick() => {
                if !ping_queue.is_empty() {
                    anyhow::bail!("[{role}] The peer did not sent a pong for previous ping on time");
                }

                // Send a randomly generated ping
                let mut payload = vec![0u8; 8];
                rand::thread_rng().fill(&mut payload[..]);
                log::debug!("[{role}] Ding, dong! It's pinging time! Sending ping {}", hex::encode(&payload));
                ping_queue.push_front(payload.clone().into());
                encrypted_writer.send(tungstenite::Message::Ping(payload.into())).await?;
            }
        }
    }

    log::debug!("[{role}] Proxy stream ended.");

    Ok(())
}
