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

use alloc::sync::Arc;
use oak_functions_lookup::LookupDataManager;
use oak_functions_wasm::{api::StdWasmApiFactory, WasmHandler};
use oak_logger::StandaloneLogger;

/// Creates a new `WasmHandler` instance.
pub fn new_wasm_handler(
    wasm_module_bytes: &[u8],
    lookup_data_manager: Arc<LookupDataManager<StandaloneLogger>>,
) -> anyhow::Result<WasmHandler<StandaloneLogger>> {
    let logger = StandaloneLogger::default();
    let wasm_api_factory = StdWasmApiFactory {
        lookup_data_manager,
    };
    WasmHandler::create(wasm_module_bytes, Arc::new(wasm_api_factory), logger)
}
