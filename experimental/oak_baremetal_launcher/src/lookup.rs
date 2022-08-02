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

use crate::schema;
use anyhow::anyhow;
use hashbrown::HashMap;
use std::fs;

pub fn encode_lookup_data<'a>(
    mut data: HashMap<Vec<u8>, Vec<u8>>,
) -> anyhow::Result<oak_idl::utils::OwnedFlatbuffer<schema::LookupData<'a>>> {
    let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
    let entries: Vec<flatbuffers::WIPOffset<schema::LookupDataEntry>> = data
        .drain()
        .map(|(key, value)| {
            let key = builder.create_vector::<u8>(&key);
            let value = builder.create_vector::<u8>(&value);
            schema::LookupDataEntry::create(
                &mut builder,
                &schema::LookupDataEntryArgs {
                    key: Some(key),
                    value: Some(value),
                },
            )
        })
        .collect();
    let items = builder.create_vector(&entries);
    let flatbuffer =
        schema::LookupData::create(&mut builder, &schema::LookupDataArgs { items: Some(items) });
    builder.finish(flatbuffer).map_err(|error| {
        anyhow!(
            "errored when encoding the lookup data as a flatbuffer: {}",
            error
        )
    })
}

pub fn load_lookup_data(
    file_path: &std::path::PathBuf,
) -> anyhow::Result<HashMap<Vec<u8>, Vec<u8>>> {
    let bytes = fs::read(&file_path).map_err(|error| {
        anyhow!(
            "Couldn't read the lookup data file {}: {}",
            file_path.display(),
            error
        )
    })?;
    oak_functions_loader::lookup_data::parse_lookup_entries(bytes.as_slice())
}
