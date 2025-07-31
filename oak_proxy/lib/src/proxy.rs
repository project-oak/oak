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

use std::{fmt, sync::Arc};

use oak_session::{ProtocolEngine, Session};
use prost::Message;
use tokio::{
    io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt},
    sync::Mutex,
};

use crate::framing::{read_message, write_message};

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

/// Pumps data from a reader to a writer, using the session to transform the
/// data.
///
/// This function is used to handle one direction of a bidirectional proxy.
///
/// - `plaintext_reader`: The source of plaintext data.
/// - `encrypted_writer`: The destination for encrypted data.
/// - `session`: The `oak_session` instance used for encryption.
async fn plaintext_to_encrypted<R, W, S, I, O>(
    mut plaintext_reader: R,
    mut encrypted_writer: W,
    session: Arc<Mutex<S>>,
) -> anyhow::Result<()>
where
    R: AsyncRead + Unpin,
    W: AsyncWrite + Unpin,
    S: ProtocolEngine<I, O> + Session,
    I: Message + Default,
    O: Message + Default,
{
    let mut buf = vec![0; 1024];
    loop {
        let n = plaintext_reader.read(&mut buf).await?;
        if n == 0 {
            break;
        }
        let mut session = session.lock().await;
        session.write(oak_proto_rust::oak::session::v1::PlaintextMessage {
            plaintext: buf[..n].to_vec(),
        })?;
        if let Some(encrypted) = session.get_outgoing_message()? {
            write_message(&mut encrypted_writer, &encrypted).await?;
        }
    }
    Ok(())
}

/// Pumps data from a reader to a writer, using the session to transform the
/// data.
///
/// This function is used to handle one direction of a bidirectional proxy.
///
/// - `encrypted_reader`: The source of encrypted data.
/// - `plaintext_writer`: The destination for plaintext data.
/// - `session`: The `oak_session` instance used for decryption.
async fn encrypted_to_plaintext<R, W, S, I, O>(
    mut encrypted_reader: R,
    mut plaintext_writer: W,
    session: Arc<Mutex<S>>,
) -> anyhow::Result<()>
where
    R: AsyncRead + Unpin,
    W: AsyncWrite + Unpin,
    S: ProtocolEngine<I, O> + Session,
    I: Message + Default,
    O: Message + Default,
{
    loop {
        let message: I = read_message(&mut encrypted_reader).await?;
        let mut session = session.lock().await;
        session.put_incoming_message(message)?;
        if let Some(plaintext) = session.read()? {
            plaintext_writer.write_all(&plaintext.plaintext).await?;
        }
    }
    #[allow(unreachable_code)]
    Ok(())
}

/// Manages a bidirectional proxy between a local stream and a remote stream.
///
/// - `plaintext_stream`: The stream connected to the local application or
///   backend.
/// - `encrypted_stream`: The stream connected to the remote proxy.
/// - `session`: The `oak_session` instance.
pub async fn proxy<S, I, O>(
    role: PeerRole,
    plaintext_stream: impl AsyncRead + AsyncWrite + Unpin + Send + 'static,
    encrypted_stream: impl AsyncRead + AsyncWrite + Unpin + Send + 'static,
    session: Arc<Mutex<S>>,
) -> anyhow::Result<()>
where
    S: ProtocolEngine<I, O> + Session + Send + 'static,
    I: Message + Default + Send + 'static,
    O: Message + Default + Send + 'static,
{
    let (plaintext_reader, plaintext_writer) = tokio::io::split(plaintext_stream);
    let (encrypted_reader, encrypted_writer) = tokio::io::split(encrypted_stream);

    let plaintext_to_encrypted_task =
        tokio::spawn(plaintext_to_encrypted(plaintext_reader, encrypted_writer, session.clone()));

    let encrypted_to_plaintext_task =
        tokio::spawn(encrypted_to_plaintext(encrypted_reader, plaintext_writer, session.clone()));

    tokio::select! {
        res = plaintext_to_encrypted_task => {
            if let Err(e) = res? {
                log::error!("[{role}] Error in plaintext-to-encrypted task: {:?}", e);
            }
        },
        res = encrypted_to_plaintext_task => {
            if let Err(e) = res? {
                log::error!("[{role}] Error in encrypted-to-plaintext task: {:?}", e);
            }
        },
    }

    log::info!("[{role}] Connection closed.");
    Ok(())
}
