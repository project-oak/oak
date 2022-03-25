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

use crate::{
    logger::Logger,
    server::{
        format_bytes, BoxedExtension, BoxedExtensionFactory, ExtensionFactory,
        OakApiNativeExtension, WasmState, ABI_USIZE,
    },
};
use oak_functions_abi::proto::OakStatus;
use oak_functions_lookup::{LookupData, LookupDataManager};
use oak_logger::OakLogger;
use std::sync::Arc;
use wasmi::ValueType;

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
        Ok(BoxedExtension::Native(Box::new(extension)))
    }
}

/// Provides logic for the host ABI function [`storage_get_item`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#storage_get_item).
pub fn storage_get_item<L: OakLogger + Clone>(
    extension: &mut LookupData<L>,
    key: Vec<u8>,
) -> Result<Vec<u8>, OakStatus> {
    extension.log_debug(&format!("storage_get_item(): key: {}", format_bytes(&key)));
    let value = extension.get(&key);
    match value {
        Some(value) => {
            // Truncate value for logging.
            let value_to_log = value.clone().into_iter().take(512).collect::<Vec<_>>();
            extension.log_debug(&format!(
                "storage_get_item(): value: {}",
                format_bytes(&value_to_log)
            ));
            Ok(value)
        }
        None => {
            extension.log_debug("storage_get_item(): value not found");
            Err(OakStatus::ErrStorageItemNotFound)
        }
    }
}

impl<L> OakApiNativeExtension for LookupData<L>
where
    L: OakLogger + Clone,
{
    fn invoke(
        &mut self,
        wasm_state: &mut WasmState,
        args: wasmi::RuntimeArgs,
    ) -> Result<Result<(), OakStatus>, wasmi::Trap> {
        let key_ptr = args.nth_checked(0)?;
        let key_len = args.nth_checked(1)?;
        let value_ptr_ptr = args.nth_checked(2)?;
        let value_len_ptr = args.nth_checked(3)?;

        let extension_args = wasm_state
            .read_extension_args(key_ptr, key_len)
            .map_err(|err| {
                self.log_error(&format!(
                    "storage_get_item(): Unable to read key from guest memory: {:?}",
                    err
                ));
                OakStatus::ErrInvalidArgs
            });

        let extension_result = extension_args
            .and_then(|key| storage_get_item(self, key))
            .and_then(|value| {
                wasm_state.write_extension_result(value, value_ptr_ptr, value_len_ptr)
            });

        Ok(extension_result)
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
}
