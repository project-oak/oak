//
// Copyright 2024 The Project Oak Authors
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

use std::sync::Arc;

use oak_functions_abi::{Request, Response};
use oak_functions_service::{lookup::LookupDataManager, Handler, Observer};

pub struct NativeHandler {
    #[allow(dead_code)]
    lookup_data_manager: Arc<LookupDataManager>,

    #[allow(dead_code)]
    observer: Option<Arc<dyn Observer + Send + Sync>>,
}

impl Handler for NativeHandler {
    type HandlerType = NativeHandler;

    fn new_handler(
        _wasm_module_bytes: &[u8],
        lookup_data_manager: Arc<LookupDataManager>,
        observer: Option<Arc<dyn Observer + Send + Sync>>,
    ) -> anyhow::Result<NativeHandler> {
        Ok(Self {
            lookup_data_manager,
            observer,
        })
    }

    fn handle_invoke(&self, invoke_request: Request) -> Result<Response, micro_rpc::Status> {
        let response_bytes = invoke_request.body;
        let invoke_response =
            Response::create(oak_functions_abi::StatusCode::Success, response_bytes);
        Ok(invoke_response)
    }
}
