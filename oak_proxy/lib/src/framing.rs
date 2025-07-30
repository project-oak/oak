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

//! A module for handling length-prefixed Protobuf messages.

use prost::Message;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};

/// Writes a length-prefixed message to the given writer.
pub async fn write_message<W, M>(writer: &mut W, message: &M) -> anyhow::Result<()>
where
    W: AsyncWrite + Unpin,
    M: Message,
{
    let encoded_message = message.encode_to_vec();
    writer.write_u32(encoded_message.len() as u32).await?;
    writer.write_all(&encoded_message).await?;
    Ok(())
}

/// Reads a length-prefixed message from the given reader.
pub async fn read_message<R, M>(reader: &mut R) -> anyhow::Result<M>
where
    R: AsyncRead + Unpin,
    M: Message + Default,
{
    let len = reader.read_u32().await?;
    let mut buffer = vec![0; len as usize];
    reader.read_exact(&mut buffer).await?;
    M::decode(buffer.as_slice()).map_err(anyhow::Error::from)
}
