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
    let encoded_lookup_data = encode_lookup_data(lookup_data, max_chunk_size)?;

    match client.update_lookup_data(&encoded_lookup_data).await {
        Ok(_) => Ok(()),
        Err(err) => Err(anyhow!("couldn't send lookup data: {:?}", err)),
    }
}

fn encode_lookup_data(
    data: HashMap<Vec<u8>, Vec<u8>>,
    max_chunk_size: ByteUnit,
) -> anyhow::Result<schema::LookupData> {
    // We will add the estimated size of ever LookupDataEntry, and to account for the LookupData
    // overhead, we generously estimate 50 bytes.
    let mut estimated_size = ByteUnit::Byte(50);

    // Overestimate delimiter size based on https://github.com/tokio-rs/prost/blob/0c350dc6ad3cd61dc9a1398dffab5ac312f3b245/src/lib.rs#L55
    let overestimated_delimiter_size = ByteUnit::Byte(10);

    let entries: Vec<schema::LookupDataEntry> = data
        .into_iter()
        .map(|(key, value)| {
            estimated_size += overestimated_delimiter_size
                + ByteUnit::Byte(key.len() as u64)
                + ByteUnit::Byte(value.len() as u64);
            schema::LookupDataEntry { key, value }
        })
        .collect();

    if estimated_size > max_chunk_size {
        Err(anyhow!(
            "lookup data size exceeds: {:?} bytes",
            max_chunk_size
        ))
    } else {
        Ok(schema::LookupData { items: entries })
    }
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
fn test_encode_lookup_data_in_bound() {
    let max_chunk_size = ByteUnit::Kibibyte(1);

    // Create data with 8 entries with 100 bytes each.
    let mut data = hashbrown::HashMap::new();
    for i in 0..8 {
        let key = format!("{:050}", i).into_bytes();
        data.insert(key.clone(), key.clone());
    }
    let result = encode_lookup_data(data, max_chunk_size);
    assert!(result.is_ok());
    assert_eq!(result.unwrap().items.len(), 8)
}

#[test]
fn test_encode_lookup_data_exceed_bound() {
    let max_chunk_size = ByteUnit::Kibibyte(1);

    // Create data with 9 entries with 100 bytes each accounting for the added overhead.
    let mut data = hashbrown::HashMap::new();
    for i in 0..9 {
        let key = format!("{:050}", i).into_bytes();
        data.insert(key.clone(), key.clone());
    }

    let result = encode_lookup_data(data, max_chunk_size);
    assert!(result.is_err())
}

#[test]
fn test_encode_lookup_data_empty() {
    let max_chunk_size = ByteUnit::Kibibyte(1);
    let data = hashbrown::HashMap::new();
    let result = encode_lookup_data(data, max_chunk_size);
    assert!(result.is_ok());
    assert_eq!(result.unwrap().items.len(), 0)
}
