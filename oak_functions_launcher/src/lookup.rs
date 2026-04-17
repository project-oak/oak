//
// Copyright 2022 The Project Oak Authors
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

use std::{fs, path::PathBuf};

use anyhow::{Context, anyhow};
use hashbrown::HashMap;
use oak_micro_rpc::oak::functions::OakFunctionsAsyncClient;
use oak_proto_rust::oak::functions::{
    Empty, ExtendNextLookupDataRequest, FinishNextLookupDataRequest, LookupDataChunk,
    LookupDataEntry, extend_next_lookup_data_request::Data,
};
use prost::Message;
use ubyte::ByteUnit;

use crate::channel::ConnectorHandle;

struct UpdateClient<'a, I: Iterator<Item = LookupDataChunk>> {
    inner: &'a mut OakFunctionsAsyncClient<ConnectorHandle>,
    chunks: I,
}

impl<I: Iterator<Item = LookupDataChunk>> UpdateClient<'_, I> {
    // Sends all chunks to the Oak Functions Service.
    async fn update(&mut self) -> anyhow::Result<()> {
        let mut next = self.chunks.next();
        while next.is_some() {
            self.extend(next).await?;
            next = self.chunks.next();
        }
        self.finish().await
    }

    async fn extend(&mut self, chunk: Option<LookupDataChunk>) -> anyhow::Result<()> {
        let _ = self
            .inner
            .extend_next_lookup_data(&ExtendNextLookupDataRequest { data: chunk.map(Data::Chunk) })
            .await
            .flatten()
            .map_err(|err| anyhow!(format!("error handling client request: {:?}", err)))?;
        Ok(())
    }

    async fn finish(&mut self) -> anyhow::Result<()> {
        let _ = self
            .inner
            .finish_next_lookup_data(&FinishNextLookupDataRequest {})
            .await
            .flatten()
            .map_err(|err| anyhow!(format!("error handling client request: {:?}", err)));
        Ok(())
    }

    #[allow(dead_code)]
    async fn abort(&mut self) -> anyhow::Result<()> {
        let _ = self
            .inner
            .abort_next_lookup_data(&Empty {})
            .await
            .flatten()
            .map_err(|err| anyhow!(format!("error handling client request: {:?}", err)));
        Ok(())
    }
}

// Loads lookup data from the given path, encodes it, and sends it to the
// client.
pub async fn update_lookup_data(
    client: &mut OakFunctionsAsyncClient<ConnectorHandle>,
    lookup_data_path: &PathBuf,
    max_chunk_size: ByteUnit,
) -> anyhow::Result<()> {
    let lookup_data = load_lookup_data(lookup_data_path)?;
    let chunks = chunk_up_lookup_data(lookup_data, max_chunk_size).into_iter();

    UpdateClient { inner: client, chunks }.update().await
}

fn chunk_up_lookup_data(
    source_lookup_data: HashMap<Vec<u8>, Vec<u8>>,
    max_chunk_size: ByteUnit,
) -> Vec<LookupDataChunk> {
    let mut chunks = Vec::new();

    // We will add the estimated size of ever LookupDataEntry, and to account for
    // the LookupData overhead, we generously estimate 50 bytes.
    let mut estimated_chunk_size = ByteUnit::Byte(50);
    // Overestimate delimiter size based on https://github.com/tokio-rs/prost/blob/0c350dc6ad3cd61dc9a1398dffab5ac312f3b245/src/lib.rs#L55
    let overestimated_delimiter_size = ByteUnit::Byte(10);

    let mut entries = Vec::new();

    for (key, value) in source_lookup_data {
        estimated_chunk_size += overestimated_delimiter_size
            + ByteUnit::Byte(key.len() as u64)
            + ByteUnit::Byte(value.len() as u64);

        // If the next element would exceed the maximum chunk size, create a new chunk.
        if estimated_chunk_size > max_chunk_size {
            chunks.push(LookupDataChunk { items: entries });
            estimated_chunk_size = ByteUnit::Byte(50);
            entries = Vec::new();
        };

        entries.push(LookupDataEntry { key: key.into(), value: value.into() })
    }
    chunks.push(LookupDataChunk { items: entries });
    chunks
}

fn load_lookup_data(file_path: &std::path::PathBuf) -> anyhow::Result<HashMap<Vec<u8>, Vec<u8>>> {
    let bytes = fs::read(file_path).map_err(|error| {
        anyhow!("couldn't read the lookup data file {}: {}", file_path.display(), error)
    })?;
    parse_lookup_entries(bytes.as_slice())
}

fn parse_lookup_entries<B: prost::bytes::Buf>(
    lookup_data_buffer: B,
) -> anyhow::Result<HashMap<Vec<u8>, Vec<u8>>> {
    let mut lookup_data_buffer = lookup_data_buffer;
    let mut entries = hashbrown::HashMap::new();
    while lookup_data_buffer.has_remaining() {
        let entry = oak_proto_rust::oak::functions::lookup_data::Entry::decode_length_delimited(
            &mut lookup_data_buffer,
        )
        .context("couldn't decode entry")?;
        entries.insert(entry.key, entry.value);
    }
    Ok(entries)
}

#[test]
fn test_chunk_up_lookup_data_in_bound() {
    let max_chunk_size = ByteUnit::Kibibyte(1);

    // Create data with 8 entries with 100 bytes each.
    let mut data = hashbrown::HashMap::new();
    for i in 0..8 {
        let key = format!("{:050}", i).into_bytes();
        data.insert(key.clone(), key.clone());
    }
    let chunks = chunk_up_lookup_data(data, max_chunk_size);
    assert_eq!(chunks.len(), 1);
    assert_eq!(chunks[0].items.len(), 8)
}

#[test]
fn test_chunk_up_lookup_data_exceed_bound() {
    let max_chunk_size = ByteUnit::Kibibyte(1);

    // Create data with 9 entries with 100 bytes each accounting for the added
    // overhead.
    let mut data = hashbrown::HashMap::new();
    for i in 0..9 {
        let key = format!("{:050}", i).into_bytes();
        data.insert(key.clone(), key.clone());
    }

    let chunks = chunk_up_lookup_data(data, max_chunk_size);
    assert_eq!(chunks.len(), 2);
    assert_eq!(chunks[0].items.len(), 8);
    assert_eq!(chunks[1].items.len(), 1)
}

#[test]
fn test_chunk_up_lookup_data_empty() {
    let max_chunk_size = ByteUnit::Kibibyte(1);
    let data = hashbrown::HashMap::new();
    let chunks = chunk_up_lookup_data(data, max_chunk_size);
    assert_eq!(chunks.len(), 1);
    assert_eq!(chunks[0].items.len(), 0)
}
