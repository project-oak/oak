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

use alloc::{
    boxed::Box,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use log::Level;
use oak_functions_abi::{proto::OakStatus, ExtensionHandle};
use oak_functions_extension::{
    BoxedExtension, BoxedExtensionFactory, ExtensionFactory, OakApiNativeExtension,
};
use oak_logger::OakLogger;
use wasmi::ValueType;

// TODO(mschett): Remove this again.
pub const ABI_USIZE: ValueType = ValueType::I32;

// TODO(#2593): Use no_std-compatible map.
use std::collections::HashMap;

use oak_functions_util::sync::Mutex;

// Host function name for invoking lookup in lookup data.
const LOOKUP_ABI_FUNCTION_NAME: &str = "storage_get_item";

pub struct LookupFactory {
    manager: Arc<LookupDataManager<Logger>>,
}

impl LookupFactory {
    pub fn new_boxed_extension_factory(
        manager: Arc<LookupDataManager<Logger>>,
    ) -> anyhow::Result<BoxedExtensionFactory> {
        let lookup_factory = Self { manager };
        Ok(Box::new(lookup_factory))
    }
}

// TODO(#2576): Move extension trait implementations to the lookup crate once the extension-related
// traits are in a separate crate.
impl ExtensionFactory for LookupFactory {
    fn create(&self) -> anyhow::Result<BoxedExtension> {
        let extension = self.manager.create_lookup_data();
        Ok(Box::new(extension))
    }
}

impl<L> OakApiNativeExtension for LookupData<L>
where
    L: OakLogger + Clone,
{
    fn invoke(&mut self, request: Vec<u8>) -> Result<Vec<u8>, OakStatus> {
        // The request is the key to lookup.
        let key = request;
        // TODO(mschett) Add logging back.
        // self.log_debug(&format!("storage_get_item(): key: {}", format_bytes(&key)));
        let value = self.get(&key);
        match value {
            Some(value) => {
                // Truncate value for logging.
                let value_to_log = value.clone().into_iter().take(512).collect::<Vec<_>>();
                // TODO(mschett) Add logging back.
                //  self.log_debug(&format!(
                //      "storage_get_item(): value: {}",
                //      format_bytes(&value_to_log)
                //  ));
                Ok(value)
            }
            // TODO(#2701): Remove ErrStorageItemNotFound from OakStatus.
            None => {
                self.log_debug("storage_get_item(): value not found");
                Err(OakStatus::ErrStorageItemNotFound)
            }
        }
    }

    fn get_metadata(&self) -> (String, wasmi::Signature) {
        let signature = wasmi::Signature::new(
            &[
                ABI_USIZE, // key_ptr
                ABI_USIZE, // key_len
                ABI_USIZE, // value_ptr_ptr
                ABI_USIZE, // value_len_ptr
            ][..],
            Some(ValueType::I32),
        );

        (LOOKUP_ABI_FUNCTION_NAME.to_string(), signature)
    }

    fn terminate(&mut self) -> anyhow::Result<()> {
        Ok(())
    }

    fn get_handle(&self) -> ExtensionHandle {
        ExtensionHandle::LookupHandle
    }
}

pub type Data = HashMap<Vec<u8>, Vec<u8>>;

/// Utility for managing lookup data.
///
/// `LookupDataManager` can be used to create `LookupData` instances that share the underlying data.
/// It can also update the underlying data. After updating the data, new `LookupData` instances will
/// use the new data, but earlier instances will still used the earlier data.
///
/// Note that the data is never mutated in-place, but only ever replaced. So instead of the Rust
/// idiom `Arc<Mutex<T>>` we have `Mutex<Arc<T>>`.
///
/// In the future we may replace both the mutex and the hash map with something like RCU.
pub struct LookupDataManager<L: OakLogger + Clone> {
    data: Mutex<Arc<Data>>,
    logger: L,
}

impl<L> LookupDataManager<L>
where
    L: OakLogger + Clone,
{
    /// Creates a new instance with empty backing data.
    pub fn new_empty(logger: L) -> Self {
        Self {
            data: Mutex::new(Arc::new(HashMap::new())),
            logger,
        }
    }

    /// Creates an instance of LookupData populated with the given entries.
    pub fn for_test(entries: Data, logger: L) -> Self {
        let data = Mutex::new(Arc::new(entries));
        Self { data, logger }
    }

    /// Updates the backing data that will be used by new `LookupData` instances.
    pub fn update_data(&self, data: Data) {
        *self.data.lock() = Arc::new(data);
    }

    /// Creates a new `LookupData` instance with a reference to the current backing data.
    pub fn create_lookup_data(&self) -> LookupData<L> {
        let data = self.data.lock().clone();
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

#[cfg(test)]
mod tests {
    use super::*;
    use maplit::hashmap;

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

        manager.update_data(hashmap! { b"key1".to_vec() => b"value1".to_vec() });
        let lookup_data_1 = manager.create_lookup_data();
        assert_eq!(lookup_data_0.len(), 0);
        assert_eq!(lookup_data_1.len(), 1);

        manager.update_data(hashmap! {
           b"key1".to_vec() => b"value1".to_vec(),
           b"key2".to_vec() => b"value2".to_vec(),
        });
        let lookup_data_2 = manager.create_lookup_data();
        assert_eq!(lookup_data_0.len(), 0);
        assert_eq!(lookup_data_1.len(), 1);
        assert_eq!(lookup_data_2.len(), 2);
    }
}
