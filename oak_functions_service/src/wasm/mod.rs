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
use alloc::{sync::Arc, vec};
use oak_functions_lookup::{LookupDataManager, LookupFactory};
use oak_functions_wasm::WasmHandler;
use oak_functions_workload_logging::WorkloadLoggingFactory;

/// Creates a new `WasmHandler` instance.
pub fn new_wasm_handler(
    wasm_module_bytes: &[u8],
    lookup_data_manager: Arc<LookupDataManager<StandaloneLogger>>,
) -> anyhow::Result<WasmHandler<StandaloneLogger>> {
    let logger = StandaloneLogger::default();
    let logging_factory = WorkloadLoggingFactory::new_boxed_extension_factory(logger.clone())?;
    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data_manager)?;
    WasmHandler::create(
        wasm_module_bytes,
        vec![logging_factory, lookup_factory],
        logger,
    )
}
