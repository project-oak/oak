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

use alloc::{format, sync::Arc};

use micro_rpc::{Status, Vec};
use oak_functions_abi::Request;
use oak_proto_rust::oak::functions::{
    AbortNextLookupDataResponse, Empty, ExtendNextLookupDataRequest, ExtendNextLookupDataResponse,
    FinishNextLookupDataRequest, FinishNextLookupDataResponse, InitializeRequest, LookupDataChunk,
    LookupDataEntry, ReserveRequest, ReserveResponse, extend_next_lookup_data_request::Data,
};
use prost::Message;

use crate::{Handler, Observer, logger::StandaloneLogger, lookup::LookupDataManager};

pub struct OakFunctionsInstance<H: Handler> {
    lookup_data_manager: Arc<LookupDataManager<128>>,
    wasm_handler: H::HandlerType,
}

impl<H: Handler> OakFunctionsInstance<H> {
    /// See [`crate::proto::oak::functions::OakFunctions::initialize`].
    pub fn new(
        request: &InitializeRequest,
        observer: Option<Arc<dyn Observer + Send + Sync>>,
        config: H::HandlerConfig,
    ) -> Result<Self, micro_rpc::Status> {
        let lookup_data_manager =
            Arc::new(LookupDataManager::new_empty(Arc::new(StandaloneLogger)));
        let wasm_handler =
            H::new_handler(config, &request.wasm_module, lookup_data_manager.clone(), observer)
                .map_err(|err| {
                    micro_rpc::Status::new_with_message(
                        micro_rpc::StatusCode::Internal,
                        format!("couldn't initialize Wasm handler: {:?}", err),
                    )
                })?;
        Ok(Self { lookup_data_manager, wasm_handler })
    }
    /// See [`crate::proto::oak::functions::OakFunctions::handle_user_request`].
    pub fn handle_user_request(&self, request: Vec<u8>) -> Result<Vec<u8>, micro_rpc::Status> {
        // TODO(#3442): Implement constant response size policy.
        self.wasm_handler.handle_invoke(Request { body: request }).map(|response| response.body)
    }
    /// See [`crate::proto::oak::functions::OakFunctions::extend_next_lookup_data`].
    pub fn extend_next_lookup_data(
        &self,
        request: ExtendNextLookupDataRequest,
    ) -> Result<ExtendNextLookupDataResponse, micro_rpc::Status> {
        let data = request.data.ok_or(micro_rpc::Status::new_with_message(
            micro_rpc::StatusCode::InvalidArgument,
            "no chunk in extend request",
        ))?;
        match data {
            Data::Chunk(ref chunk) => {
                self.lookup_data_manager.extend_next_lookup_data(to_data(chunk))
            }
            Data::LengthDelimitedEntries(mut data) => {
                while let Ok(entry) = LookupDataEntry::decode_length_delimited(&mut data) {
                    // Grabbing the mutex for each insert seems to be faster than grabbing the mutex
                    // before the while loop.
                    self.lookup_data_manager.insert(&entry.key, &entry.value)
                }
            }
        }
        Ok(ExtendNextLookupDataResponse {})
    }

    pub fn extend_lookup_data_chunk(
        &self,
        chunk: LookupDataChunk,
    ) -> Result<(), micro_rpc::Status> {
        self.lookup_data_manager.extend_next_lookup_data(to_data(&chunk));
        Ok(())
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

    pub fn reserve(&self, request: ReserveRequest) -> Result<ReserveResponse, Status> {
        self.lookup_data_manager
            .reserve(request.additional_entries)
            .map(|()| ReserveResponse {})
            .map_err(|err| {
                micro_rpc::Status::new_with_message(
                    micro_rpc::StatusCode::ResourceExhausted,
                    format!("failed to reserve memory: {:?}", err),
                )
            })
    }
}

// Helper function to convert [`LookupDataChunk`] to [`Data`].
fn to_data(chunk: &LookupDataChunk) -> impl Iterator<Item = (&[u8], &[u8])> {
    chunk.items.iter().map(|entry| (entry.key.as_ref(), entry.value.as_ref()))
}

#[cfg(test)]
mod tests {
    use bytes::{Bytes, BytesMut};

    use super::*;
    use crate::wasm::{WasmConfig, WasmHandler};

    static ITEMS: [LookupDataEntry; 2] = [
        LookupDataEntry { key: Bytes::from_static(b"key1"), value: Bytes::from_static(b"value1") },
        LookupDataEntry { key: Bytes::from_static(b"key2"), value: Bytes::from_static(b"value2") },
    ];

    #[test]
    fn test_extend_chunk() {
        let wasm_module_path = "oak_functions/examples/echo/echo.wasm";

        let wasm_module = std::fs::read(wasm_module_path).unwrap();

        let instance = OakFunctionsInstance::<WasmHandler>::new(
            &InitializeRequest { wasm_module, constant_response_size: 0 },
            None,
            WasmConfig::default(),
        )
        .unwrap();

        instance
            .extend_next_lookup_data(ExtendNextLookupDataRequest {
                data: Some(Data::Chunk(LookupDataChunk { items: ITEMS.clone().into() })),
            })
            .unwrap();
        instance.finish_next_lookup_data(FinishNextLookupDataRequest {}).unwrap();
        let lookup_data = instance.lookup_data_manager.create_lookup_data();
        for LookupDataEntry { key, value } in &ITEMS {
            assert_eq!(Some(&value[..]), lookup_data.get(key));
        }
        assert_eq!(None, lookup_data.get(b"key3"));
    }

    #[test]
    fn test_extend_entries() {
        let wasm_module_path = "oak_functions/examples/echo/echo.wasm";

        let wasm_module = std::fs::read(wasm_module_path).unwrap();

        let instance = OakFunctionsInstance::<WasmHandler>::new(
            &InitializeRequest { wasm_module, constant_response_size: 0 },
            None,
            WasmConfig::default(),
        )
        .unwrap();

        let mut entries = BytesMut::new();
        for item in &ITEMS {
            item.encode_length_delimited(&mut entries).unwrap();
        }

        instance
            .extend_next_lookup_data(ExtendNextLookupDataRequest {
                data: Some(Data::LengthDelimitedEntries(entries.into())),
            })
            .unwrap();
        instance.finish_next_lookup_data(FinishNextLookupDataRequest {}).unwrap();
        let lookup_data = instance.lookup_data_manager.create_lookup_data();
        for LookupDataEntry { key, value } in &ITEMS {
            assert_eq!(Some(&value[..]), lookup_data.get(key));
        }
        assert_eq!(None, lookup_data.get(b"key3"));
    }
}
