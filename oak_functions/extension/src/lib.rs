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

use oak_functions_abi::proto::{ExtensionHandle, OakStatus};
use oak_logger::OakLogger;

/// A OakApiNativeExtension implements new functionality for the Oak Functions Runtime.
pub trait OakApiNativeExtension: Send + Sync {
    /// Invokes the extension with the given request and returns a result. If no result
    /// is expected, the result is empty.  An error within the extension is reflected in the
    /// `OakStatus`.
    /// TODO(#2701): Stop returning OakStatus for errors internal to extensions.
    fn invoke(&mut self, request: Vec<u8>) -> Result<Vec<u8>, OakStatus>;

    /// Metadata about this Extension, including the exported host function name, the function's
    /// signature, and the corresponding ExtensionHandle.
    /// TODO(#2752): Remove once we call all extensions with invoke.
    fn get_metadata(&self) -> (String, wasmi::Signature);

    /// Performs any cleanup or terminating behavior necessary before destroying the WasmState.
    fn terminate(&mut self) -> anyhow::Result<()>;

    /// Gets the `ExtensionHandle` for this extension.
    fn get_handle(&self) -> ExtensionHandle;
}

/// An ExtensionFactory creates a new [`OakApiNativeExtension`].
pub trait ExtensionFactory<L: OakLogger>: Send + Sync {
    fn create(&self) -> anyhow::Result<Box<dyn OakApiNativeExtension>>;
}
