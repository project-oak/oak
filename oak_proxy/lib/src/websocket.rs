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

//! A module for handling WebSocket messages.

use futures::{SinkExt, StreamExt};
use prost::Message;
use tokio::net::TcpStream;
use tokio_tungstenite::{
    MaybeTlsStream, WebSocketStream, tungstenite::protocol::Message as TungsteniteMessage,
};

/// Writes a Protobuf message to the given WebSocket stream.
pub async fn write_message<M>(
    stream: &mut WebSocketStream<MaybeTlsStream<TcpStream>>,
    message: &M,
) -> anyhow::Result<()>
where
    M: Message,
{
    let encoded_message = message.encode_to_vec();
    stream.send(TungsteniteMessage::Binary(encoded_message.into())).await?;
    Ok(())
}

/// Reads a Protobuf message from the given WebSocket stream.
pub async fn read_message<M>(
    stream: &mut WebSocketStream<MaybeTlsStream<TcpStream>>,
) -> anyhow::Result<M>
where
    M: Message + Default,
{
    let message = stream.next().await.ok_or(anyhow::anyhow!("stream closed"))??;
    match message {
        TungsteniteMessage::Binary(bytes) => M::decode(&bytes[..]).map_err(anyhow::Error::from),
        _ => Err(anyhow::anyhow!("unexpected message type: {:?}", message)),
    }
}
