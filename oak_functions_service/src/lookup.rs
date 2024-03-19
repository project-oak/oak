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

use alloc::{
    format,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};

use log::{info, Level};

use crate::{logger::OakLogger, lookup_htbl::LookupHtbl};

// Data maintains the invariant on lookup data to have [at most one
// value](https://github.com/project-oak/oak/tree/main/oak/oak_functions_service/README.md#invariant-at-most-one-value)
type Data = LookupHtbl;

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
    /// Build data from the builder and set the builder back to the initial
    /// state.
    fn build(&mut self) -> Data {
        self.state = BuilderState::Empty;
        core::mem::take(&mut self.data)
    }

    /// Extends the DataBuilder with new data.
    ///
    /// Note, if new data contains a key already present in the existing data,
    /// calling extend overwrites the value.
    fn extend<'a, T: IntoIterator<Item = (&'a [u8], &'a [u8])>>(&mut self, new_data: T) {
        self.state = BuilderState::Extending;
        self.data.extend(new_data)
    }

    fn reserve(&mut self, additional_entries: usize) {
        self.data.reserve(additional_entries)
    }
}

/// Utility for managing lookup data.
///
/// `LookupDataManager` can be used to create `LookupData` instances that share
/// the underlying data. It can also update the underlying data. After updating
/// the data, new `LookupData` instances will use the new data, but earlier
/// instances will still used the earlier data.
///
/// LookupDataManager maintains the invariants [consistent view on lookup
/// data](https://github.com/project-oak/oak/tree/main/oak/oak_functions_service/README.md##invariant-consistent-view-on-lookup-data) , and [shared
/// lookup data](https://github.com/project-oak/oak/tree/main/oak/oak_functions_service/README.md##invariant-shared-lookup-data)
///
/// Note that the data is never mutated in-place, but only ever replaced. So
/// instead of the Rust idiom `Arc<Spinlock<T>>` we have `Spinlock<Arc<T>>`.
///
/// In the future we may replace both the mutex and the hash map with something
/// like RCU.
pub struct LookupDataManager {
    #[cfg(feature = "std")]
    data: parking_lot::RwLock<Arc<Data>>,
    #[cfg(not(feature = "std"))]
    data: spinning_top::RwSpinlock<Arc<Data>>,
    // Behind a lock, because we have multiple references to LookupDataManager and need to mutate
    // data builder.
    #[cfg(feature = "std")]
    data_builder: parking_lot::Mutex<DataBuilder>,
    #[cfg(not(feature = "std"))]
    data_builder: spinning_top::Spinlock<DataBuilder>,
    logger: Arc<dyn OakLogger>,
}

impl LookupDataManager {
    /// Creates a new instance with empty backing data.
    pub fn new_empty(logger: Arc<dyn OakLogger>) -> Self {
        Self {
            #[cfg(feature = "std")]
            data: parking_lot::RwLock::new(Arc::new(Data::default())),
            #[cfg(not(feature = "std"))]
            data: spinning_top::RwSpinlock::new(Arc::new(Data::default())),
            // Incrementally builds the backing data that will be used by new `LookupData`
            // instances when finished.
            #[cfg(feature = "std")]
            data_builder: parking_lot::Mutex::new(DataBuilder::default()),
            #[cfg(not(feature = "std"))]
            data_builder: spinning_top::Spinlock::new(DataBuilder::default()),
            logger,
        }
    }

    /// Creates an instance of LookupData populated with the given entries.
    pub fn for_test(data: Vec<(Vec<u8>, Vec<u8>)>, logger: Arc<dyn OakLogger>) -> Self {
        let test_manager = Self::new_empty(logger);
        test_manager.reserve(data.len() as u64).unwrap();
        test_manager.extend_next_lookup_data(data.iter().map(|(k, v)| (k.as_ref(), v.as_ref())));
        test_manager.finish_next_lookup_data();
        test_manager
    }

    pub fn reserve(&self, additional_entries: u64) -> anyhow::Result<()> {
        let mut data_builder = self.data_builder.lock();
        data_builder.reserve(additional_entries as usize);
        Ok(())
    }

    pub fn extend_next_lookup_data<'a, T: IntoIterator<Item = (&'a [u8], &'a [u8])>>(
        &self,
        new_data: T,
    ) {
        info!("Start extending next lookup data");
        {
            let mut data_builder = self.data_builder.lock();
            data_builder.extend(new_data);
        }
        info!("Finish extending next lookup data");
    }

    // Finish building the next lookup data and replace the current lookup data in
    // place.
    pub fn finish_next_lookup_data(&self) {
        let data_len;
        let next_data_len;
        info!("Start replacing lookup data by next lookup data");
        {
            let mut data_builder = self.data_builder.lock();
            let next_data = data_builder.build();
            next_data_len = next_data.len();
            let mut data = self.data.write();
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

    /// Creates a new `LookupData` instance with a reference to the current
    /// backing data.
    pub fn create_lookup_data(&self) -> LookupData {
        let keys;
        let data = {
            let data = self.data.read().clone();
            keys = data.len();
            LookupData::new(data, self.logger.clone())
        };
        info!("Created lookup data with len: {}", keys);
        data
    }
}

/// Provides access to shared lookup data.
#[derive(Clone)]
pub struct LookupData {
    data: Arc<Data>,
    logger: Arc<dyn OakLogger>,
}

impl LookupData {
    fn new(data: Arc<Data>, logger: Arc<dyn OakLogger>) -> Self {
        Self { data, logger }
    }

    /// Gets an individual entry from the backing data.
    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        self.data.get(key)
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

/// Returns a slice covering up to the first `limit` elements of the given
/// slice.
pub fn limit<T>(slice: &[T], limit: usize) -> &[T] {
    &slice[..limit.min(slice.len())]
}

/// Converts a binary sequence to a string if it is a valid UTF-8 string, or
/// formats it as a numeric vector of bytes otherwise.
pub fn format_bytes(v: &[u8]) -> String {
    alloc::str::from_utf8(v).map(|s| s.to_string()).unwrap_or_else(|_| format!("{:?}", v))
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::*;

    #[derive(Clone)]
    struct TestLogger;

    impl OakLogger for TestLogger {
        fn log_sensitive(&self, _level: Level, _message: &str) {}
        fn log_public(&self, _level: Level, _message: &str) {}
    }

    #[test]
    fn test_lookup_data_instance_consistency() {
        // Ensure that the data for a specific lookup data instance remains consistent
        // even if the data in the manager has been updated.
        let manager = LookupDataManager::new_empty(Arc::new(TestLogger));
        let lookup_data_0 = manager.create_lookup_data();
        assert_eq!(lookup_data_0.len(), 0);

        reserve_and_extend_test_data(&manager, 0, 1);
        let lookup_data_1 = manager.create_lookup_data();
        assert_eq!(lookup_data_0.len(), 0);
        assert_eq!(lookup_data_1.len(), 1);

        // Creating test data in the same range replaces some keys.
        reserve_and_extend_test_data(&manager, 0, 2);

        let lookup_data_2 = manager.create_lookup_data();
        assert_eq!(lookup_data_0.len(), 0);
        assert_eq!(lookup_data_1.len(), 1);
        assert_eq!(lookup_data_2.len(), 2);
    }

    #[test]
    fn test_update_lookup_data_one_chunk() {
        let manager = LookupDataManager::new_empty(Arc::new(TestLogger));
        reserve_and_extend_test_data(&manager, 0, 2);
        let lookup_data = manager.create_lookup_data();
        assert_eq!(lookup_data.len(), 2);
    }

    #[test]
    fn test_update_lookup_data_two_chunks() {
        let manager = LookupDataManager::new_empty(Arc::new(TestLogger));
        let lookup_data_0 = manager.create_lookup_data();

        manager.reserve(4).unwrap();
        manager.extend_next_lookup_data(
            create_test_data(0, 2).iter().map(|(k, v)| (k.as_ref(), v.as_ref())),
        );
        let lookup_data_1 = manager.create_lookup_data();

        manager.extend_next_lookup_data(
            create_test_data(2, 4).iter().map(|(k, v)| (k.as_ref(), v.as_ref())),
        );
        manager.finish_next_lookup_data();
        let lookup_data_2 = manager.create_lookup_data();

        assert_eq!(lookup_data_0.len(), 0);
        assert_eq!(lookup_data_1.len(), 0);
        assert_eq!(lookup_data_2.len(), 4);
    }

    #[test]
    fn test_update_lookup_four_chunks() {
        let manager = LookupDataManager::new_empty(Arc::new(TestLogger));

        manager.reserve(7).unwrap();
        manager.extend_next_lookup_data(
            create_test_data(0, 2).iter().map(|(k, v)| (k.as_ref(), v.as_ref())),
        );
        manager.extend_next_lookup_data(
            create_test_data(2, 3).iter().map(|(k, v)| (k.as_ref(), v.as_ref())),
        );
        // Note the overlap which results in a bit of wasted space.
        manager.extend_next_lookup_data(
            create_test_data(2, 6).iter().map(|(k, v)| (k.as_ref(), v.as_ref())),
        );
        manager.extend_next_lookup_data(
            create_test_data(6, 7).iter().map(|(k, v)| (k.as_ref(), v.as_ref())),
        );
        manager.finish_next_lookup_data();

        let lookup_data = manager.create_lookup_data();

        assert_eq!(lookup_data.len(), 7);
    }

    #[test]
    fn test_update_lookup_data_abort_by_sender() {
        let manager = LookupDataManager::new_empty(Arc::new(TestLogger));
        let lookup_data_0 = manager.create_lookup_data();

        manager.reserve(2).unwrap();
        manager.extend_next_lookup_data(
            create_test_data(0, 2).iter().map(|(k, v)| (k.as_ref(), v.as_ref())),
        );
        manager.abort_next_lookup_data();
        let lookup_data_1 = manager.create_lookup_data();

        manager.reserve(1).unwrap();
        manager.extend_next_lookup_data(
            create_test_data(0, 1).iter().map(|(k, v)| (k.as_ref(), v.as_ref())),
        );
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

    // Create test data with size distinct keys between inclusive start and
    // exclusive end.
    fn create_test_data(start: i32, end: i32) -> Vec<(Vec<u8>, Vec<u8>)> {
        let mut vec: Vec<(Vec<u8>, Vec<u8>)> =
            Vec::with_capacity((end - start).try_into().unwrap());
        for i in start..end {
            vec.push((format!("key{}", i).into_bytes(), format!("value{}", i).into_bytes()));
        }
        vec
    }

    fn reserve_and_extend_test_data(manager: &LookupDataManager, start: i32, end: i32) {
        manager.reserve((end - start) as u64).unwrap();
        manager.extend_next_lookup_data(
            create_test_data(start, end).iter().map(|(k, v)| (k.as_ref(), v.as_ref())),
        );
        manager.finish_next_lookup_data();
    }
}
