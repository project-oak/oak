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

use crate::logger::StandaloneLogger;
use alloc::vec;
use oak_functions_wasm::WasmHandler;
use oak_functions_workload_logging::WorkloadLoggingFactory;
use oak_remote_attestation::crypto::get_sha256;

/// Creates a new `WasmHandler` instance.
pub fn new_wasm_handler() -> anyhow::Result<WasmHandler<StandaloneLogger>> {
    // We can't yet send the Wasm module bytes from the loader, so we use an embedded Wasm module.
    let wasm_module_bytes = include_bytes!("echo.wasm");
    let logger = StandaloneLogger::default();
    let logging_factory = WorkloadLoggingFactory::new_boxed_extension_factory(logger.clone())?;
    let wasm_hash = get_sha256(wasm_module_bytes).to_vec();
    WasmHandler::create(wasm_module_bytes, wasm_hash, vec![logging_factory], logger)
}
