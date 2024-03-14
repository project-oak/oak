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

use alloc::vec;

use anyhow::Result;

use crate::Channel;

/// Reads a chunk of data and acknowledges the transmission by writing back the
/// number of bytes read.
fn read_chunk<C: Channel + ?Sized>(channel: &mut C, chunk: &mut [u8]) -> Result<()> {
    let len: u32 = chunk.len().try_into().map_err(|_| anyhow::anyhow!("chunk too big"))?;
    channel.read_exact(chunk)?;
    channel.write_all(&len.to_le_bytes())
}

/// Loads a Restricted Application over the given channel using a basic framed
/// format.
///
/// This is intended for use after the kernel has started up to load the
/// Restricted Application, before we start the application and hand off the
/// channel to it.
///
/// The protocol to load the application is very simple:
/// 1. loader sends the size of the application binary, as u32
/// 2. loader sends MAX_SIZE of data and waits for the kernel to acknowledge
/// 3. kernel reads up to MAX_SIZE of data and acks by responding with the
///    amount of data read
/// 4. repeat (2) and (3) until all the data has been transmitted
pub fn load_raw<C: Channel + ?Sized, const MAX_SIZE: usize>(
    channel: &mut C,
) -> Result<vec::Vec<u8>> {
    let payload_len = {
        let mut buf: [u8; 4] = Default::default();
        channel.read_exact(&mut buf)?;
        u32::from_le_bytes(buf)
    };
    let mut payload = vec![0; payload_len as usize];
    let mut chunks_mut = payload.array_chunks_mut::<MAX_SIZE>();

    for chunk in chunks_mut.by_ref() {
        read_chunk(channel, chunk)?;
    }
    read_chunk(channel, chunks_mut.into_remainder())?;

    Ok(payload)
}
