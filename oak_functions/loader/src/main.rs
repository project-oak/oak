//
// Copyright 2021 The Project Oak Authors
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

// Required for enabling benchmark tests.
#![feature(test)]

use anyhow::Context;
use prost::Message;
use std::{collections::HashMap, fs, sync::RwLock};
use structopt::StructOpt;

mod server;

use crate::server::create_and_start_server;

#[cfg(test)]
mod tests;

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.functions.lookup_data.rs"));
}

/// Command line options for the Oak loader.
#[derive(StructOpt, Clone, Debug)]
#[structopt(about = "Oak Functions Loader")]
pub struct Opt {
    #[structopt(
        long,
        default_value = "8080",
        help = "Port number that the server listens on."
    )]
    http_listen_port: u16,
    #[structopt(
        long,
        help = "Path to a Wasm file to be loaded and executed per invocation. The Wasm module must export a function named `main`."
    )]
    wasm_path: String,
    // TODO(#1930): Support downloading lookup data from a URL instead of a local file.
    // TODO(#1930): Support periodically re-downloading lookup data at a given time interval.
    #[structopt(
        long,
        help = "Path to a file to load for data lookups, containing key / value entries in protobuf binary format."
    )]
    lookup_data_path: String,
}

struct LookupData {
    lookup_data_path: String,
    entries: RwLock<HashMap<Vec<u8>, Vec<u8>>>,
}

impl LookupData {
    /// Creates a new [`LookupData`] instance that can refresh its internal entries from the
    /// provided data file path.
    ///
    /// Entries in the data file path must be consecutive binary encoded and length delimited
    /// protobuf messages according to the definition in `/oak_functions/proto/lookup_data.proto`.
    ///
    /// The returned instance is empty, and must be populated by calling the [`LookupData::refresh`]
    /// method at least once.
    fn new_empty(lookup_data_path: &str) -> LookupData {
        LookupData {
            lookup_data_path: lookup_data_path.to_string(),
            entries: RwLock::new(HashMap::new()),
        }
    }

    /// Refreshes the internal entries of this struct from the data file path provided at
    /// construction time.
    ///
    /// If successful, entries are completely replaced (i.e. not merged).
    ///
    /// If there is any error while reading or parsing the data, an error is returned by this
    /// method, and existing entries are left untouched. The caller may retry the refresh operation
    /// at a future time.
    fn refresh(&self) -> anyhow::Result<()> {
        // TODO(#1930): Avoid loading the entire file in memory for parsing.
        let lookup_data_buf =
            fs::read(&self.lookup_data_path).context("could not read lookup data file")?;
        let entries = load_lookup_entries(&mut lookup_data_buf.as_ref())
            .context("could not parse lookup data")?;
        log::info!("loaded {} entries of lookup data", entries.len());

        // This block is here to emphasize and ensure that the write lock is only held for a very
        // short time.
        {
            *self
                .entries
                .write()
                .expect("could not lock entries for write") = entries;
        }

        Ok(())
    }

    /// Convenience getter for an individual entry that reduces lock contention by cloning the
    /// resulting value as quickly as possible and returning it instead of a reference.
    #[allow(dead_code)]
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        self.entries
            .read()
            .expect("could not lock entries for read")
            .get(key)
            .cloned()
    }

    #[allow(dead_code)]
    fn len(&self) -> usize {
        self.entries
            .read()
            .expect("could not lock entries for read")
            .len()
    }
}

fn load_lookup_entries<B: bytes::Buf>(
    lookup_data_buffer: B,
) -> anyhow::Result<HashMap<Vec<u8>, Vec<u8>>> {
    let mut lookup_data_buffer = lookup_data_buffer;
    let mut entries = HashMap::new();
    while lookup_data_buffer.has_remaining() {
        let entry = proto::Entry::decode_length_delimited(&mut lookup_data_buffer)
            .context("could not decode entry")?;
        entries.insert(entry.key, entry.value);
    }
    Ok(entries)
}

/// Main execution point for the Oak Functions Loader.
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    if cfg!(feature = "oak-unsafe") {
        env_logger::init();
    } else {
        eprintln!("No debugging output configured at build time");
    }
    let opt = Opt::from_args();

    // For now the server runs in the same thread, so `notify_sender` is not really needed.
    let (_notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    let wasm_module_bytes = fs::read(&opt.wasm_path)
        .with_context(|| format!("Couldn't read Wasm file {}", &opt.wasm_path))?;

    let lookup_data = LookupData::new_empty(&opt.lookup_data_path);
    if !opt.lookup_data_path.is_empty() {
        lookup_data
            .refresh()
            .context("could not load lookup data")?;
    }

    // TODO(#1930): Pass lookup data to the server instance.

    // Start HTTP server.
    let address = format!("[::]:{}", &opt.http_listen_port);
    create_and_start_server(&address, &wasm_module_bytes, notify_receiver).await
}
