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

// Loads lookup data from the given path, encodes it, and sends it to the client.
pub async fn update_lookup_data(
    client: &mut OakFunctionsAsyncClient<ConnectorHandle>,
    lookup_data_path: &PathBuf,
) -> anyhow::Result<()> {
    let lookup_data = load_lookup_data(lookup_data_path)?;
    let encoded_lookup_data = encode_lookup_data(lookup_data)?;

    match client.update_lookup_data(&encoded_lookup_data).await {
        Ok(_) => Ok(()),
        Err(err) => Err(anyhow!("couldn't send lookup data: {:?}", err)),
    }
}

fn encode_lookup_data(data: HashMap<Vec<u8>, Vec<u8>>) -> anyhow::Result<schema::LookupData> {
    let entries: Vec<schema::LookupDataEntry> = data
        .into_iter()
        .map(|(key, value)| schema::LookupDataEntry { key, value })
        .collect();
    Ok(schema::LookupData { items: entries })
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
