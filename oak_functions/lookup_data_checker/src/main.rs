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

use anyhow::Context;
use clap::Parser;
use location_utils::{cell_id_from_bytes, location_from_bytes, LOCATION_SIZE, S2_DEFAULT_LEVEL};
use log::{debug, info};
use prost::Message;
use std::{
    collections::{HashMap, HashSet},
    fs::File,
    io::{BufReader, Read},
};

#[derive(Parser, Clone, Debug)]
#[command(about = "Oak Functions Lookup Data Checker")]
pub struct Opt {
    #[arg(long)]
    file_path: String,
}

pub fn parse_lookup_entries<B: prost::bytes::Buf>(
    lookup_data_buffer: B,
) -> anyhow::Result<HashMap<Vec<u8>, Vec<u8>>> {
    let mut lookup_data_buffer = lookup_data_buffer;
    let mut entries = HashMap::new();
    while lookup_data_buffer.has_remaining() {
        let entry =
            oak_functions_proto::oak::oak_functions::lookup_data::Entry::decode_length_delimited(
                &mut lookup_data_buffer,
            )
            .map_err(|err| anyhow::anyhow!("couldn't decode entry: {err}"))?;
        entries.insert(entry.key, entry.value);
    }
    Ok(entries)
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::parse();

    // Read lookup data file.
    info!("Checking lookup data file format: {}", opt.file_path);
    let file = File::open(opt.file_path).context("couldn't open file")?;
    let mut reader = BufReader::new(file);
    let mut buffer = Vec::new();
    reader.read_to_end(&mut buffer)?;
    let entries =
        parse_lookup_entries(&mut buffer.as_ref()).context("couldn't parse lookup data")?;

    // Parse lookup data entries.
    debug!("Parsed entries:");
    let mut weather_locations = HashSet::new();
    let mut cell_locations = HashSet::new();
    for entry in entries {
        if entry.0.len() == LOCATION_SIZE {
            let location = location_from_bytes(&entry.0)
                .with_context(|| format!("couldn't parse location {:?}", &entry.0))?;
            weather_locations.insert(entry.0);

            debug!("- {{{:?}: {:?}}} # Location", location, entry.1.to_vec());
        } else {
            let cell_id = cell_id_from_bytes(&entry.0)
                .with_context(|| format!("couldn't parse cell ID {:?}", &entry.0))?;
            assert_eq!(cell_id.level(), S2_DEFAULT_LEVEL as u64);

            let mut locations = vec![];
            for chunk in entry.1.chunks(LOCATION_SIZE) {
                let location = location_from_bytes(chunk).with_context(|| {
                    format!(
                        "couldn't parse location {:?} corresponding to the cell ID {:?}",
                        chunk, cell_id
                    )
                })?;
                locations.push(location);
                cell_locations.insert(chunk.to_vec());
            }

            debug!("- {{{:?}: {:?}}} # Cell ID", cell_id, locations);
        }
    }

    // Check that all locations are present in the Cell IDs.
    if weather_locations != cell_locations {
        let extra_locations: HashSet<_> = weather_locations.difference(&cell_locations).collect();
        if !extra_locations.is_empty() {
            anyhow::bail!(format!(
                "locations are not presented in Cell IDs: {:?}",
                extra_locations
            ));
        }

        let extra_locations_in_cells: HashSet<_> =
            cell_locations.difference(&weather_locations).collect();
        if !extra_locations_in_cells.is_empty() {
            anyhow::bail!(format!(
                "locations from Cell IDs do not have individual data entries: {:?}",
                extra_locations
            ));
        }
    }

    info!("Format is correct");
    Ok(())
}
