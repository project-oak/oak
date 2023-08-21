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

use super::{WasmApi, WasmApiFactory};
use crate::{
    logger::{OakLogger, StandaloneLogger},
    lookup::{format_bytes, LookupData, LookupDataManager},
};
use alloc::{boxed::Box, format, sync::Arc, vec::Vec};
use log::Level;
use oak_functions_sdk::proto::oak::functions::wasm::v1::{
    LogRequest, LogResponse, LookupDataRequest, LookupDataResponse, ReadRequestRequest,
    ReadRequestResponse, StdWasmApi, StdWasmApiServer, TestRequest, TestResponse,
    WriteResponseRequest, WriteResponseResponse,
};
use spinning_top::Spinlock;

/// The main purpose of this factory is to allow creating a new instance of the
/// [`StdWasmApiImpl`] for each incoming gRPC request, with an immutable snapshot of the
/// current lookup data.
pub struct StdWasmApiFactory {
    pub lookup_data_manager: Arc<LookupDataManager<StandaloneLogger>>,
}

impl WasmApiFactory<StandaloneLogger> for StdWasmApiFactory {
    fn create_wasm_api(
        &self,
        request: Vec<u8>,
        response: Arc<Spinlock<Vec<u8>>>,
    ) -> Box<dyn WasmApi> {
        Box::new(StdWasmApiImpl {
            lookup_data: self.lookup_data_manager.create_lookup_data(),
            logger: StandaloneLogger::default(),
            request,
            response,
        })
    }
}

/// Implementation of the standard Oak Functions API.
///
/// There are probably more locks than necessary here, it should be possible to reduce them in the
/// future.
#[derive(Clone)]
pub struct StdWasmApiImpl {
    lookup_data: LookupData<StandaloneLogger>,
    logger: StandaloneLogger,
    /// Current request, as received from the client.
    request: Vec<u8>,
    /// Current response, as received from the Wasm module.
    response: Arc<Spinlock<Vec<u8>>>,
}

impl StdWasmApi for StdWasmApiImpl {
    fn read_request(
        &mut self,
        _: ReadRequestRequest,
    ) -> Result<ReadRequestResponse, micro_rpc::Status> {
        self.logger
            .log_sensitive(Level::Debug, "invoked read_request");
        Ok(ReadRequestResponse {
            body: self.request.clone(),
        })
    }
    fn write_response(
        &mut self,
        req: WriteResponseRequest,
    ) -> Result<WriteResponseResponse, micro_rpc::Status> {
        self.logger
            .log_sensitive(Level::Debug, "invoked write_response");
        *self.response.lock() = req.body;
        Ok(WriteResponseResponse::default())
    }

    fn log(&mut self, request: LogRequest) -> Result<LogResponse, ::micro_rpc::Status> {
        self.logger.log_sensitive(Level::Debug, "invoked log");
        self.logger
            .log_sensitive(Level::Debug, &format!("[Wasm] {}", request.message));
        Ok(LogResponse::default())
    }

    fn lookup_data(
        &mut self,
        request: LookupDataRequest,
    ) -> Result<LookupDataResponse, ::micro_rpc::Status> {
        self.logger
            .log_sensitive(Level::Debug, "invoked lookup_data");
        // The request is the key to lookup.
        let key = request.key;
        let key_to_log = key.iter().take(512).cloned().collect::<Vec<_>>();
        self.logger.log_sensitive(
            Level::Debug,
            &format!("storage_get_item(): key: {}", format_bytes(&key_to_log)),
        );
        let value = self.lookup_data.get(&key);

        // Log found value.
        value.clone().map_or_else(
            || {
                self.logger
                    .log_sensitive(Level::Debug, "storage_get_item(): value not found");
            },
            |value| {
                // Truncate value for logging.
                let value_to_log = value.into_iter().take(512).collect::<Vec<_>>();
                self.logger.log_sensitive(
                    Level::Debug,
                    &format!("storage_get_item(): value: {}", format_bytes(&value_to_log)),
                );
            },
        );

        Ok(LookupDataResponse { value })
    }

    fn test(&mut self, req: TestRequest) -> Result<TestResponse, micro_rpc::Status> {
        self.logger.log_sensitive(Level::Debug, "invoked test");
        Ok(TestResponse {
            body: if req.echo { req.body } else { Vec::new() },
        })
    }
}

impl WasmApi for StdWasmApiImpl {
    fn transport(&mut self) -> Box<dyn micro_rpc::Transport<Error = !>> {
        Box::new(StdWasmApiServer::new(self.clone()))
    }
}
