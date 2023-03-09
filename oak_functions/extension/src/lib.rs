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

#![no_std]

extern crate alloc;

use alloc::{boxed::Box, vec::Vec};
use oak_functions_abi::proto::{ExtensionHandle, OakStatus};
use oak_logger::OakLogger;

/// A OakApiNativeExtension implements new functionality for the Oak Functions Runtime.
pub trait OakApiNativeExtension: Send + Sync {
    /// Invokes the extension with the given request and returns a result. If no result
    /// is expected, the result is empty.  An error within the extension is reflected in the
    /// `OakStatus`.
    fn invoke(&mut self, request: Vec<u8>) -> Result<Vec<u8>, OakStatus>;

    /// Performs any cleanup or terminating behavior necessary before destroying the WasmState.
    fn terminate(&mut self) -> anyhow::Result<()>;

    /// Gets the `ExtensionHandle` for this extension.
    fn get_handle(&self) -> ExtensionHandle;
}

impl alloc::fmt::Debug for dyn OakApiNativeExtension {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_fmt(format_args!("OakApiNativeExtenxion {:?}", self))
    }
}

/// An ExtensionFactory creates a new [`OakApiNativeExtension`].
pub trait ExtensionFactory<L: OakLogger>: Send + Sync {
    fn create(&self) -> anyhow::Result<Box<dyn OakApiNativeExtension>>;
}
