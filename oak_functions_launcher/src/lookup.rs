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

use crate::{
    channel::ConnectorHandle,
    schema::{self, OakFunctionsAsyncClient},
};
use anyhow::{anyhow, Context};
use hashbrown::HashMap;
use prost::Message;
use std::{fs, path::PathBuf};
use ubyte::ByteUnit;

// Loads lookup data from the given path, encodes it, and sends it to the client.
pub async fn update_lookup_data(
    client: &mut OakFunctionsAsyncClient<ConnectorHandle>,
    lookup_data_path: &PathBuf,
) -> anyhow::Result<()> {
    // Fix the maximum size of a chunk to the proto limit size of 2 GiB.
    let max_chunk_size = ByteUnit::Gibibyte(2);

    let lookup_data = load_lookup_data(lookup_data_path)?;
    let mut chunks = chunk_up_lookup_data(lookup_data, max_chunk_size);

    // We currently send only if we can fit the data in one chunk, otherwise we return an error.
    // TODO(#3718): to send more than one chunk.
    if chunks.len() != 1 {
        return Err(anyhow!(
            "lookup data size exceeds: {:?} bytes",
            max_chunk_size
        ));
    }
    let chunk = chunks.pop().unwrap();

    let action = schema::UpdateAction::StartAndFinish;
    let request = schema::UpdateLookupDataRequest {
        action: action.into(),
        chunk: Some(chunk),
    };

    match client.update_lookup_data(&request).await {
        Ok(_) => Ok(()),
        Err(err) => Err(anyhow!("couldn't send lookup data: {:?}", err)),
    }
}

fn chunk_up_lookup_data(
    source_lookup_data: HashMap<Vec<u8>, Vec<u8>>,
    max_chunk_size: ByteUnit,
) -> Vec<schema::LookupDataChunk> {
    let mut chunks = Vec::new();

    // We will add the estimated size of ever LookupDataEntry, and to account for the LookupData
    // overhead, we generously estimate 50 bytes.
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
            chunks.push(schema::LookupDataChunk { items: entries });
            estimated_chunk_size = ByteUnit::Byte(50);
            entries = Vec::new();
        };

        entries.push(schema::LookupDataEntry { key, value })
    }
    chunks.push(schema::LookupDataChunk { items: entries });
    chunks
}

fn load_lookup_data(file_path: &std::path::PathBuf) -> anyhow::Result<HashMap<Vec<u8>, Vec<u8>>> {
    let bytes = fs::read(file_path).map_err(|error| {
        anyhow!(
            "couldn't read the lookup data file {}: {}",
            file_path.display(),
            error
        )
    })?;
    parse_lookup_entries(bytes.as_slice())
}

fn parse_lookup_entries<B: prost::bytes::Buf>(
    lookup_data_buffer: B,
) -> anyhow::Result<HashMap<Vec<u8>, Vec<u8>>> {
    let mut lookup_data_buffer = lookup_data_buffer;
    let mut entries = HashMap::new();
    while lookup_data_buffer.has_remaining() {
        let entry =
            oak_functions_abi::proto::Entry::decode_length_delimited(&mut lookup_data_buffer)
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

    // Create data with 9 entries with 100 bytes each accounting for the added overhead.
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
