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
#![no_std]

extern crate alloc;
// We use the std crate for now until we have no_std-compatible replacements for the map and
// read-write lock.
extern crate std;

use alloc::{sync::Arc, vec::Vec};
use log::Level;
use oak_logger::OakLogger;

// TODO(#2593): Use no_std-compatible map.
use std::collections::HashMap;

// TODO(#2579): Use no_std-compatible RwLock implementation once available.
use std::sync::RwLock;

pub type Data = HashMap<Vec<u8>, Vec<u8>>;

/// Utility for managing lookup data.
///
/// `LookupDataManager` can be used to create `LookupData` instances that shared the underlying
/// data. It can also update the underlying data. After updating the data, new `LookupData` instance
/// will use the new data, but earlier instances will still used the earlier data.
pub struct LookupDataManager<L: OakLogger + Clone> {
    data: RwLock<Arc<Data>>,
    logger: L,
}

impl<L> LookupDataManager<L>
where
    L: OakLogger + Clone,
{
    /// Creates a new instance with empty backing data.
    pub fn new_empty(logger: L) -> Self {
        Self {
            data: RwLock::new(Arc::new(HashMap::new())),
            logger,
        }
    }

    /// Creates an instance of LookupData populated with the given entries.
    pub fn for_test(entries: Data, logger: L) -> Self {
        let data = RwLock::new(Arc::new(entries));
        Self { data, logger }
    }

    /// Updates the backing data that will be used by new `LookupData` instances.
    pub fn update_data(&self, data: Data) {
        *self.data.write().expect("could not lock data for read") = Arc::new(data);
    }

    /// Creates a new `LookupData` instance with a reference to the current backing data.
    pub fn create_lookup_data(&self) -> LookupData<L> {
        let data = self
            .data
            .read()
            .expect("could not lock data for read")
            .clone();
        LookupData::new(data, self.logger.clone())
    }
}

/// Provides access to shared lookup data.
pub struct LookupData<L: OakLogger + Clone> {
    data: Arc<Data>,
    logger: L,
}

impl<L> LookupData<L>
where
    L: OakLogger + Clone,
{
    fn new(data: Arc<Data>, logger: L) -> Self {
        Self { data, logger }
    }

    /// Gets an individual entry from the backing data.
    pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        self.data.get(key).cloned()
    }

    /// Gets the number of entries in the backing data.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Whether the backing data is empty.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Logs an error message.
    ///
    /// The code assumes the message might contain sensitive information.
    pub fn log_error(&self, message: &str) {
        self.logger.log_sensitive(Level::Error, message)
    }

    /// Logs a debug message.
    ///
    /// The code assumes the message might contain sensitive information.
    pub fn log_debug(&self, message: &str) {
        self.logger.log_sensitive(Level::Debug, message)
    }
}
