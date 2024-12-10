//
// Copyright 2024 The Project Oak Authors
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

use alloc::vec::Vec;

use anyhow::{Context, Result};
use prost::Message;

/// Trait for passing incomplete evidence between layers of software components.
///
/// For example, in DICE it is used to pass the DiceData containing the
/// certificate authority private key, and for TDX it is used to pass an
/// unfinished EventLog.
pub trait Serializable: Sized {
    fn deserialize(bytes: &[u8]) -> Result<Self>;
    fn serialize(self) -> Vec<u8>;
}

/// Tries to decode a custom length delimited encoding into a proto message.
///
/// This format is used for consistency across platforms and languages. The
/// first 8 bytes of the slice is interpreted as the length of the encoded proto
/// message as a little-endian unsigned integer. The following slice of that
/// length is then parsed as a proto message.
pub fn try_decode_length_delimited_proto<T: Message + core::default::Default>(
    buffer: &[u8],
) -> Result<T> {
    let (size_bytes, rest) = buffer.split_at(core::mem::size_of::<usize>());

    let len = usize::from_le_bytes(
        size_bytes
            .try_into()
            .map_err(anyhow::Error::msg)
            .context("buffer doesn't contain a length prefix")?,
    );
    if len > rest.len() {
        anyhow::bail!("invalid buffer length");
    }
    T::decode(&rest[..len]).map_err(anyhow::Error::msg).context("couldn't parse proto message")
}

/// Encodes a proto message into a custom length delimited format.
///
/// This format is used for consistency across platforms and languages. The
/// first 8 bytes contains the length of the encoded message in bytes as a
/// little endian unsigned integer. This is followed by the actual encoded
/// message.
pub fn encode_length_delimited_proto<T: Message>(message: &T) -> Vec<u8> {
    let len = message.encoded_len();
    let mut result = Vec::with_capacity(len + core::mem::size_of::<usize>());
    result.extend_from_slice(&len.to_le_bytes());
    // Ok to unwrap, since this will only panic if the vec doesn't have sufficient
    // capacity.
    message.encode(&mut result).unwrap();
    result
}
