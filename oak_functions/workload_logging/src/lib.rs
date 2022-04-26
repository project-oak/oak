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

use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
    vec::Vec,
};
use log::Level;
use oak_functions_abi::{proto::OakStatus, ExtensionHandle};
use oak_functions_extension::{ExtensionFactory, OakApiNativeExtension};
use oak_logger::OakLogger;
use wasmi::ValueType;

// TODO(#2752): Remove once we call all extensions with invoke.
const ABI_USIZE: ValueType = ValueType::I32;

// Host function name for invoking lookup in lookup data.
const LOG_ABI_FUNCTION_NAME: &str = "write_log_message";

pub struct WorkloadLoggingFactory<L: OakLogger> {
    logger: L,
}

impl<L> WorkloadLoggingFactory<L>
where
    L: OakLogger + 'static,
{
    pub fn new_boxed_extension_factory(logger: L) -> anyhow::Result<Box<dyn ExtensionFactory<L>>> {
        let logging_factory = Self { logger };
        Ok(Box::new(logging_factory))
    }
}

impl<L> ExtensionFactory<L> for WorkloadLoggingFactory<L>
where
    L: OakLogger + 'static,
{
    fn create(&self) -> anyhow::Result<Box<dyn OakApiNativeExtension>> {
        let extension = WorkloadLogger::new(self.logger.clone());
        Ok(Box::new(extension))
    }
}

/// Wrapper that uses the underlying logger to provide workload logging.
pub struct WorkloadLogger<L: OakLogger + Clone> {
    logger: L,
}

impl<L> WorkloadLogger<L>
where
    L: OakLogger + Clone,
{
    fn new(logger: L) -> Self {
        Self { logger }
    }
}

impl<L: OakLogger> OakApiNativeExtension for WorkloadLogger<L> {
    fn invoke(&mut self, request: Vec<u8>) -> Result<Vec<u8>, OakStatus> {
        // The request is the UTF-8 encoded message to log.
        let log_message = core::str::from_utf8(&request).map_err(|err| {
            self.logger.log_sensitive(
                Level::Warn,
                &format!(
                    "workload_logging: Request is not a valid UTF-8 encoded string: {:?}\nContent: {:?}",
                    err, request
                ),
            );
            OakStatus::ErrInvalidArgs
        })?;
        self.logger
            .log_sensitive(Level::Debug, &format!("[Wasm] {}", log_message));
        Ok(Vec::new())
    }

    fn get_metadata(&self) -> (String, wasmi::Signature) {
        let signature = wasmi::Signature::new(
            &[
                ABI_USIZE, // buf_ptr
                ABI_USIZE, // buf_len
            ][..],
            Some(ValueType::I32),
        );

        (LOG_ABI_FUNCTION_NAME.to_string(), signature)
    }

    fn terminate(&mut self) -> anyhow::Result<()> {
        Ok(())
    }

    fn get_handle(&self) -> ExtensionHandle {
        ExtensionHandle::LoggingHandle
    }
}
