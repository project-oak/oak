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
    schema::{self, LookupDataChunk, OakFunctionsAsyncClient, UpdateAction, UpdateStatus},
};
use anyhow::{anyhow, Context};
use async_recursion::async_recursion;
use hashbrown::HashMap;
use prost::Message;
use std::{fs, path::PathBuf, vec::IntoIter};
use ubyte::ByteUnit;

struct UpdateClient<'a> {
    inner: &'a mut OakFunctionsAsyncClient<ConnectorHandle>,
    chunks: IntoIter<LookupDataChunk>,
}

impl UpdateClient<'_> {
    async fn start(&mut self) -> anyhow::Result<()> {
        // Send the current chunk first.
        let update_response = self.send_request(UpdateAction::Start).await?;
        if UpdateStatus::Started != update_response.update_status() {
            return Err(anyhow!("Did not receive expected update status: Started"));
        };
        self.continue_().await
    }

    #[async_recursion]
    async fn continue_(&mut self) -> anyhow::Result<()> {
        if self.chunks.len() == 1 {
            self.finish().await
        } else {
            let update_response = self.send_request(UpdateAction::Continue).await?;
            if UpdateStatus::Started != update_response.update_status() {
                return Err(anyhow!("Did not receive expected update status: Started"));
            };
            self.continue_().await
        }
    }

    async fn finish(&mut self) -> anyhow::Result<()> {
        let update_response = self.send_request(UpdateAction::Finish).await?;
        if UpdateStatus::Finished != update_response.update_status() {
            return Err(anyhow!("Did not receive expected update status: Finished"));
        };
        Ok(())
    }

    async fn start_and_finish(&mut self) -> anyhow::Result<()> {
        let update_response = self.send_request(UpdateAction::StartAndFinish).await?;
        if UpdateStatus::Finished != update_response.update_status() {
            return Err(anyhow!("Did not receive expected update status: Finished"));
        };
        Ok(())
    }

    // Helper to send a request with the given action.
    async fn send_request(
        &mut self,
        action: schema::UpdateAction,
    ) -> anyhow::Result<schema::UpdateLookupDataResponse> {
        let request = schema::UpdateLookupDataRequest {
            action: action.into(),
            chunk: self.chunks.next(),
        };

        self.inner
            .update_lookup_data(&request)
            .await
            .flatten()
            .map_err(|err| anyhow!(format!("error handling client request: {:?}", err)))
    }
}

// Loads lookup data from the given path, encodes it, and sends it to the client.
pub async fn update_lookup_data(
    client: &mut OakFunctionsAsyncClient<ConnectorHandle>,
    lookup_data_path: &PathBuf,
    max_chunk_size: ByteUnit,
) -> anyhow::Result<()> {
    let lookup_data = load_lookup_data(lookup_data_path)?;
    let chunks = chunk_up_lookup_data(lookup_data, max_chunk_size).into_iter();

    let mut update_client = UpdateClient {
        inner: client,
        chunks,
    };

    if update_client.chunks.len() == 1 {
        update_client.start_and_finish().await
    } else {
        update_client.start().await
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
