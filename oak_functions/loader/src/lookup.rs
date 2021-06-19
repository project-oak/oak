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

use crate::logger::Logger;
use anyhow::Context;
use hyper_rustls::HttpsConnector;
use log::Level;
use prost::Message;
use std::{collections::HashMap, sync::RwLock, time::Instant};

/// An in-memory lookup store instance that can refresh its internal entries from the provided data
/// file URL.
///
/// Entries in the data file path must be consecutive binary encoded and length delimited
/// protobuf messages according to the definition in `/oak_functions/proto/lookup_data.proto`.
pub struct LookupData {
    lookup_data_url: String,
    entries: RwLock<HashMap<Vec<u8>, Vec<u8>>>,
    logger: Logger,
}

impl LookupData {
    /// Creates a new empty [`LookupData`] instance that can refresh its internal entries from the
    /// provided data file URL.
    ///
    /// The returned instance is empty, and must be populated by calling the [`LookupData::refresh`]
    /// method at least once.
    pub fn new_empty(lookup_data_url: &str, logger: Logger) -> LookupData {
        LookupData {
            lookup_data_url: lookup_data_url.to_string(),
            entries: RwLock::new(HashMap::new()),
            logger,
        }
    }

    /// Refreshes the internal entries of this struct from the data file URL provided at
    /// construction time.
    ///
    /// If successful, entries are completely replaced (i.e. not merged).
    ///
    /// If there is any error while reading or parsing the data, an error is returned by this
    /// method, and existing entries are left untouched. The caller may retry the refresh operation
    /// at a future time.
    pub async fn refresh(&self) -> anyhow::Result<()> {
        // TODO(#1930): Avoid loading the entire file in memory for parsing.
        let https = HttpsConnector::with_native_roots();
        let client = hyper::Client::builder().build::<_, hyper::Body>(https);
        let res = client
            .get(
                self.lookup_data_url
                    .parse()
                    .context("could not parse lookup data URL")?,
            )
            .await
            .context("could not fetch lookup data")?;

        let start = Instant::now();
        let lookup_data_buf = hyper::body::to_bytes(res.into_body())
            .await
            .context("could not read lookup data response body")?;
        self.logger.log_public(
            Level::Info,
            &format!(
                "downloaded {} bytes of lookup data in {:.0?}",
                lookup_data_buf.len(),
                start.elapsed()
            ),
        );

        let start = Instant::now();
        let entries = parse_lookup_entries(&mut lookup_data_buf.as_ref())
            .context("could not parse lookup data")?;

        self.logger.log_public(
            Level::Info,
            &format!(
                "parsed {} entries of lookup data in {:.0?}",
                entries.len(),
                start.elapsed()
            ),
        );

        // This block is here to emphasize and ensure that the write lock is only held for a very
        // short time.
        let start = Instant::now();
        {
            *self
                .entries
                .write()
                .expect("could not lock entries for write") = entries;
        }
        self.logger.log_public(
            Level::Debug,
            &format!(
                "lookup data write lock acquisition time: {:.0?}",
                start.elapsed()
            ),
        );

        Ok(())
    }

    /// Convenience getter for an individual entry that reduces lock contention by cloning the
    /// resulting value as quickly as possible and returning it instead of a reference.
    pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        self.entries
            .read()
            .expect("could not lock entries for read")
            .get(key)
            .cloned()
    }

    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.entries
            .read()
            .expect("could not lock entries for read")
            .len()
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.entries
            .read()
            .expect("could not lock entries for read")
            .is_empty()
    }
}

pub fn parse_lookup_entries<B: prost::bytes::Buf>(
    lookup_data_buffer: B,
) -> anyhow::Result<HashMap<Vec<u8>, Vec<u8>>> {
    let mut lookup_data_buffer = lookup_data_buffer;
    let mut entries = HashMap::new();
    while lookup_data_buffer.has_remaining() {
        let entry =
            oak_functions_abi::proto::Entry::decode_length_delimited(&mut lookup_data_buffer)
                .context("could not decode entry")?;
        entries.insert(entry.key, entry.value);
    }
    Ok(entries)
}
