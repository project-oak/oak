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
    lookup_data::LookupData,
    server::{
        format_bytes, AbiPointer, AbiPointerOffset, BoxedExtension, BoxedExtensionFactory,
        ExtensionFactory, OakApiNativeExtension, WasmState, ABI_USIZE,
    },
};
use log::Level;
use oak_functions_abi::proto::OakStatus;
use oak_logger::OakLogger;
use std::sync::Arc;
use wasmi::ValueType;

// Host function name for invoking lookup in lookup data.
const LOOKUP_ABI_FUNCTION_NAME: &str = "storage_get_item";

pub struct LookupExtension {
    lookup_data: Arc<LookupData>,
    logger: Logger,
}

pub struct LookupFactory {
    lookup_data: Arc<LookupData>,
    logger: Logger,
}

impl LookupFactory {
    pub fn new_boxed_extension_factory(
        lookup_data: Arc<LookupData>,
        logger: Logger,
    ) -> anyhow::Result<BoxedExtensionFactory> {
        let lookup_factory = Self {
            lookup_data,
            logger,
        };
        Ok(Box::new(lookup_factory))
    }
}

impl ExtensionFactory for LookupFactory {
    fn create(&self) -> anyhow::Result<BoxedExtension> {
        let extension = LookupExtension {
            lookup_data: self.lookup_data.clone(),
            logger: self.logger.clone(),
        };
        Ok(BoxedExtension::Native(Box::new(extension)))
    }
}

/// Corresponds to the host ABI function [`storage_get_item`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#storage_get_item).
pub fn storage_get_item(
    wasm_state: &mut WasmState,
    extension: &mut LookupExtension,
    key_ptr: AbiPointer,
    key_len: AbiPointerOffset,
    value_ptr_ptr: AbiPointer,
    value_len_ptr: AbiPointer,
) -> Result<(), OakStatus> {
    let key = wasm_state
        .get_memory()
        .get(key_ptr, key_len as usize)
        .map_err(|err| {
            extension.logger.log_sensitive(
                Level::Error,
                &format!(
                    "storage_get_item(): Unable to read key from guest memory: {:?}",
                    err
                ),
            );
            OakStatus::ErrInvalidArgs
        })?;
    extension.logger.log_sensitive(
        Level::Debug,
        &format!("storage_get_item(): key: {}", format_bytes(&key)),
    );
    match extension.lookup_data.get(&key) {
        Some(value) => {
            // Truncate value for logging.
            let value_to_log = value.clone().into_iter().take(512).collect::<Vec<_>>();
            extension.logger.log_sensitive(
                Level::Debug,
                &format!("storage_get_item(): value: {}", format_bytes(&value_to_log)),
            );
            let dest_ptr = wasm_state.alloc(value.len() as u32);
            wasm_state.write_buffer_to_wasm_memory(&value, dest_ptr)?;
            wasm_state.write_u32_to_wasm_memory(dest_ptr, value_ptr_ptr)?;
            wasm_state.write_u32_to_wasm_memory(value.len() as u32, value_len_ptr)?;
            Ok(())
        }
        None => {
            extension
                .logger
                .log_sensitive(Level::Debug, "storage_get_item(): value not found");
            Err(OakStatus::ErrStorageItemNotFound)
        }
    }
}

impl OakApiNativeExtension for LookupExtension {
    fn invoke(
        &mut self,
        wasm_state: &mut WasmState,
        args: wasmi::RuntimeArgs,
    ) -> Result<Result<(), OakStatus>, wasmi::Trap> {
        Ok(storage_get_item(
            wasm_state,
            self,
            args.nth_checked(0)?,
            args.nth_checked(1)?,
            args.nth_checked(2)?,
            args.nth_checked(3)?,
        ))
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
