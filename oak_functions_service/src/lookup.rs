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

use crate::logger::OakLogger;
use alloc::{
    format,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use bytes::Bytes;
use hashbrown::HashMap;
use log::{info, Level};
use spinning_top::Spinlock;

// Data maintains the invariant on lookup data to have [at most one
// value](https://github.com/project-oak/oak/tree/main/oak/oak_functions_service/README.md#invariant-at-most-one-value)
pub type Data = HashMap<Bytes, Bytes>;

#[derive(Default)]
enum BuilderState {
    #[default]
    Empty,
    Extending,
}

// Incrementally build next lookup data keeping track of the state.
#[derive(Default)]
struct DataBuilder {
    data: Data,
    state: BuilderState,
}

impl DataBuilder {
    /// Build data from the builder and set the builder back to the initial state.
    fn build(&mut self) -> Data {
        self.state = BuilderState::Empty;
        core::mem::take(&mut self.data)
    }

    /// Extends the DataBuilder with new data.
    ///
    /// Note, if new data contains a key already present in the existing data, calling extend
    /// overwrites the value.
    fn extend<T: IntoIterator<Item = (Bytes, Bytes)>>(&mut self, new_data: T) {
        self.state = BuilderState::Extending;
        self.data.extend(new_data);
    }

    fn reserve(&mut self, additional: usize) -> anyhow::Result<()> {
        self.data
            .try_reserve(additional)
            .map_err(|err| anyhow::anyhow!("failed to reserve memory: {:?}", err))
    }
}

/// Utility for managing lookup data.
///
/// `LookupDataManager` can be used to create `LookupData` instances that share the underlying data.
/// It can also update the underlying data. After updating the data, new `LookupData` instances will
/// use the new data, but earlier instances will still used the earlier data.
///
/// LookupDataManager maintains the invariants [consistent view on lookup
/// data](https://github.com/project-oak/oak/tree/main/oak/oak_functions_service/README.md##invariant-consistent-view-on-lookup-data) , and [shared
/// lookup data](https://github.com/project-oak/oak/tree/main/oak/oak_functions_service/README.md##invariant-shared-lookup-data)
///
/// Note that the data is never mutated in-place, but only ever replaced. So instead of the Rust
/// idiom `Arc<Spinlock<T>>` we have `Spinlock<Arc<T>>`.
///
/// In the future we may replace both the mutex and the hash map with something like RCU.
pub struct LookupDataManager<L: OakLogger + Clone> {
    data: Spinlock<Arc<Data>>,
    // Behind a lock, because we have multiple references to LookupDataManager and need to mutate
    // data builder.
    data_builder: Spinlock<DataBuilder>,
    logger: L,
}

impl<L> LookupDataManager<L>
where
    L: OakLogger + Clone,
{
    /// Creates a new instance with empty backing data.
    pub fn new_empty(logger: L) -> Self {
        Self {
            data: Spinlock::new(Arc::new(Data::new())),
            // Incrementally builds the backing data that will be used by new `LookupData`
            // instances when finished.
            data_builder: Spinlock::new(DataBuilder::default()),
            logger,
        }
    }

    /// Creates an instance of LookupData populated with the given entries.
    pub fn for_test(data: Data, logger: L) -> Self {
        let test_manager = Self::new_empty(logger);
        *test_manager.data.lock() = Arc::new(data);
        test_manager
    }

    pub fn reserve(&self, additional: u64) -> anyhow::Result<()> {
        let mut data_builder = self.data_builder.lock();
        data_builder.reserve(
            additional
                .try_into()
                .map_err(|err| anyhow::anyhow!("error converting integer: {:?}", err))?,
        )
    }

    pub fn extend_next_lookup_data<T: IntoIterator<Item = (Bytes, Bytes)>>(&self, new_data: T) {
        info!("Start extending next lookup data");
        {
            let mut data_builder = self.data_builder.lock();
            data_builder.extend(new_data);
        }
        info!("Finish extending next lookup data");
    }

    // Finish building the next lookup data and replace the current lookup data in place.
    pub fn finish_next_lookup_data(&self) {
        let data_len;
        let next_data_len;
        info!("Start replacing lookup data by next lookup data");
        {
            let mut data_builder = self.data_builder.lock();
            let next_data = data_builder.build();
            next_data_len = next_data.len();
            let mut data = self.data.lock();
            data_len = data.len();
            *data = Arc::new(next_data);
        }
        info!(
            "Finished replacing lookup data with len {} by next lookup data with len {}",
            data_len, next_data_len
        );
    }

    pub fn abort_next_lookup_data(&self) {
        info!("Start aborting next lookup data");
        {
            let mut data_builder = self.data_builder.lock();
            // Clear the builder throwing away the intermediate result.
            let _ = data_builder.build();
        }
        info!("Finish aborting next lookup data");
    }

    /// Creates a new `LookupData` instance with a reference to the current backing data.
    pub fn create_lookup_data(&self) -> LookupData<L> {
        let keys;
        let data = {
            let data = self.data.lock().clone();
            keys = data.len();
            LookupData::new(data, self.logger.clone())
        };
        info!("Created lookup data with len: {}", keys);
        data
    }
}

/// Provides access to shared lookup data.
#[derive(Clone)]
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
        self.data.get(key).cloned().map(Into::into)
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

/// Returns a slice covering up to the first `limit` elements of the given slice.
pub fn limit<T>(slice: &[T], limit: usize) -> &[T] {
    &slice[..limit.min(slice.len())]
}

/// Converts a binary sequence to a string if it is a valid UTF-8 string, or formats it as a numeric
/// vector of bytes otherwise.
pub fn format_bytes(v: &[u8]) -> String {
    alloc::str::from_utf8(v)
        .map(|s| s.to_string())
        .unwrap_or_else(|_| format!("{:?}", v))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone)]
    struct TestLogger {}
    impl OakLogger for TestLogger {
        fn log_sensitive(&self, _level: Level, _message: &str) {}
        fn log_public(&self, _level: Level, _message: &str) {}
    }

    #[test]
    fn test_lookup_data_instance_consistency() {
        // Ensure that the data for a specific lookup data instance remains consistent even if the
        // data in the manager has been updated.
        let manager = LookupDataManager::new_empty(TestLogger {});
        let lookup_data_0 = manager.create_lookup_data();
        assert_eq!(lookup_data_0.len(), 0);

        manager.extend_next_lookup_data(create_test_data(0, 1));
        manager.finish_next_lookup_data();
        let lookup_data_1 = manager.create_lookup_data();
        assert_eq!(lookup_data_0.len(), 0);
        assert_eq!(lookup_data_1.len(), 1);

        // Creating test data in the same range replaces some keys.
        manager.extend_next_lookup_data(create_test_data(0, 2));
        manager.finish_next_lookup_data();

        let lookup_data_2 = manager.create_lookup_data();
        assert_eq!(lookup_data_0.len(), 0);
        assert_eq!(lookup_data_1.len(), 1);
        assert_eq!(lookup_data_2.len(), 2);
    }

    #[test]
    fn test_update_lookup_data_one_chunk() {
        let manager = LookupDataManager::new_empty(TestLogger {});
        manager.extend_next_lookup_data(create_test_data(0, 2));
        manager.finish_next_lookup_data();
        let lookup_data = manager.create_lookup_data();
        assert_eq!(lookup_data.len(), 2);
    }

    #[test]
    fn test_update_lookup_data_two_chunks() {
        let manager = LookupDataManager::new_empty(TestLogger {});
        let lookup_data_0 = manager.create_lookup_data();

        manager.extend_next_lookup_data(create_test_data(0, 2));
        let lookup_data_1 = manager.create_lookup_data();

        manager.extend_next_lookup_data(create_test_data(2, 4));
        manager.finish_next_lookup_data();
        let lookup_data_2 = manager.create_lookup_data();

        assert_eq!(lookup_data_0.len(), 0);
        assert_eq!(lookup_data_1.len(), 0);
        assert_eq!(lookup_data_2.len(), 4);
    }

    #[test]
    fn test_update_lookup_four_chunks() {
        let manager = LookupDataManager::new_empty(TestLogger {});

        manager.extend_next_lookup_data(create_test_data(0, 2));
        manager.extend_next_lookup_data(create_test_data(2, 3));
        // We have one key overlapping here.
        manager.extend_next_lookup_data(create_test_data(2, 6));
        manager.extend_next_lookup_data(create_test_data(6, 7));
        manager.finish_next_lookup_data();

        let lookup_data = manager.create_lookup_data();

        assert_eq!(lookup_data.len(), 7);
    }

    #[test]
    fn test_update_lookup_data_abort_by_sender() {
        let manager = LookupDataManager::new_empty(TestLogger {});
        let lookup_data_0 = manager.create_lookup_data();

        manager.extend_next_lookup_data(create_test_data(0, 2));
        manager.abort_next_lookup_data();
        let lookup_data_1 = manager.create_lookup_data();

        manager.extend_next_lookup_data(create_test_data(0, 1));
        manager.finish_next_lookup_data();
        let lookup_data_2 = manager.create_lookup_data();

        assert_eq!(lookup_data_0.len(), 0);
        assert_eq!(lookup_data_1.len(), 0);
        assert_eq!(lookup_data_2.len(), 1);
    }

    #[test]
    fn test_format_bytes() {
        // Valid UTF-8 string.
        assert_eq!("🚀oak⭐", format_bytes("🚀oak⭐".as_bytes()));
        // Incorrect UTF-8 bytes, as per https://doc.rust-lang.org/std/string/struct.String.html#examples-3.
        assert_eq!("[0, 159, 146, 150]", format_bytes(&[0, 159, 146, 150]));
    }

    // Create test data with size distinct keys between inclusive start and exclusive end.
    fn create_test_data(start: i32, end: i32) -> Data {
        HashMap::from_iter((start..end).map(|i| {
            (
                format!("key{}", i).into_bytes().into(),
                format!("value{}", i).into_bytes().into(),
            )
        }))
    }
}
