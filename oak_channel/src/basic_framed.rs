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

//! Basic framed format for use before the channel is handed off to the
//! application.
//!
//! This protocol is used twice.
//! 1. To load the application. Here the host is the sender, enclave is the
//!    recipient.
//! 2. To return the attestation evidence. Here the host is the recipient,
//!    enclave is the sender.
//!
//! The protocol is very simple:
//! 1. sender sends the size of the payload, as u32
//! 2. sender sends MAX_SIZE of data and waits for the recipient to acknowledge
//! 3. recipient reads up to MAX_SIZE of data and acks by responding with the
//!    amount of data read
//! 4. repeat (2) and (3) until all the data has been transmitted

use alloc::vec;

use anyhow::Result;

use crate::Channel;

const MAX_SIZE: usize = 4096;

/// Reads a chunk of data and acknowledges the transmission by writing back the
/// number of bytes read.
fn read_chunk<C: Channel + ?Sized>(channel: &mut C, chunk: &mut [u8]) -> Result<()> {
    let len: u32 = chunk.len().try_into().map_err(|_| anyhow::anyhow!("chunk too big"))?;
    channel.read_exact(chunk)?;
    channel.write_all(&len.to_le_bytes())
}

pub fn receive_raw<C: Channel + ?Sized>(channel: &mut C) -> Result<vec::Vec<u8>> {
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

pub fn send_raw<C: Channel + ?Sized>(channel: &mut C, payload: &[u8]) -> Result<()> {
    channel
        .write_all(&(payload.len() as u32).to_le_bytes())
        .expect("failed to send application binary length to enclave");

    // Write a chunk of data and await the recipients acknowledgement.
    let mut write_chunk = move |chunk| {
        channel.write_all(chunk)?;
        let mut ack: [u8; 4] = Default::default();
        channel.read_exact(&mut ack)?;
        if u32::from_le_bytes(ack) as usize != chunk.len() {
            anyhow::bail!("ack wasn't of correct length");
        }
        Ok(())
    };

    // The kernel expects data to be transmitted in chunks of one page.
    let mut chunks = payload.array_chunks::<MAX_SIZE>();
    for chunk in chunks.by_ref() {
        write_chunk(chunk)?;
    }
    write_chunk(chunks.remainder())?;

    Ok(())
}
