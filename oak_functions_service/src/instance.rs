//
// Copyright 2023 The Project Oak Authors
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
    logger::StandaloneLogger,
    lookup::LookupDataManager,
    proto::oak::functions::{
        AbortNextLookupDataResponse, Empty, ExtendNextLookupDataRequest,
        ExtendNextLookupDataResponse, FinishNextLookupDataRequest, FinishNextLookupDataResponse,
        InitializeRequest, LookupDataChunk,
    },
    wasm,
};
use alloc::{format, sync::Arc};
use bytes::Bytes;
use micro_rpc::{Status, Vec};
use oak_functions_abi::Request;

pub struct OakFunctionsInstance {
    lookup_data_manager: Arc<LookupDataManager<StandaloneLogger>>,
    wasm_handler: wasm::WasmHandler<StandaloneLogger>,
}

impl OakFunctionsInstance {
    /// See [`crate::proto::oak::functions::OakFunctions::initialize`].
    pub fn new(request: &InitializeRequest) -> Result<Self, micro_rpc::Status> {
        let lookup_data_manager =
            Arc::new(LookupDataManager::new_empty(StandaloneLogger::default()));
        let wasm_handler =
            wasm::new_wasm_handler(&request.wasm_module, lookup_data_manager.clone()).map_err(
                |err| {
                    micro_rpc::Status::new_with_message(
                        micro_rpc::StatusCode::Internal,
                        format!("couldn't initialize Wasm handler: {:?}", err),
                    )
                },
            )?;
        Ok(Self {
            lookup_data_manager,
            wasm_handler,
        })
    }
    /// See [`crate::proto::oak::functions::OakFunctions::handle_user_request`].
    pub fn handle_user_request(&self, request: Vec<u8>) -> Result<Vec<u8>, micro_rpc::Status> {
        // TODO(#3442): Implement constant response size policy.
        self.wasm_handler
            .handle_invoke(Request { body: request })
            .map(|response| response.body)
    }
    /// See [`crate::proto::oak::functions::OakFunctions::extend_next_lookup_data`].
    pub fn extend_next_lookup_data(
        &self,
        request: ExtendNextLookupDataRequest,
    ) -> Result<ExtendNextLookupDataResponse, micro_rpc::Status> {
        self.lookup_data_manager
            .extend_next_lookup_data(to_data(request.chunk.ok_or(
                micro_rpc::Status::new_with_message(
                    micro_rpc::StatusCode::InvalidArgument,
                    "no chunk in extend request",
                ),
            )?));
        Ok(ExtendNextLookupDataResponse {})
    }
    /// See [`crate::proto::oak::functions::OakFunctions::finish_next_lookup_data`].
    pub fn finish_next_lookup_data(
        &self,
        _request: FinishNextLookupDataRequest,
    ) -> Result<FinishNextLookupDataResponse, micro_rpc::Status> {
        self.lookup_data_manager.finish_next_lookup_data();
        Ok(FinishNextLookupDataResponse {})
    }
    /// See [`crate::proto::oak::functions::OakFunctions::abort_next_lookup_data`].
    pub fn abort_next_lookup_data(
        &self,
        _request: Empty,
    ) -> Result<AbortNextLookupDataResponse, Status> {
        self.lookup_data_manager.abort_next_lookup_data();
        Ok(AbortNextLookupDataResponse {})
    }
}

// Helper function to convert [`LookupDataChunk`] to [`Data`].
fn to_data(chunk: LookupDataChunk) -> impl Iterator<Item = (Bytes, Bytes)> {
    chunk
        .items
        .into_iter()
        .map(|entry| (entry.key, entry.value))
}
