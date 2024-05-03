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

use alloc::{boxed::Box, rc::Rc, sync::Arc, vec::Vec};
use core::cell::Cell;

use log::Level;
use oak_functions_sdk::proto::oak::functions::wasm::v1::{
    BytesValue, LogRequest, LogResponse, LookupDataMultiRequest, LookupDataMultiResponse,
    LookupDataRequest, LookupDataResponse, ReadRequestRequest, ReadRequestResponse, StdWasmApi,
    StdWasmApiServer, TestRequest, TestResponse, WriteResponseRequest, WriteResponseResponse,
};

use super::{WasmApi, WasmApiFactory};
use crate::{
    logger::{OakLogger, StandaloneLogger},
    lookup::{LookupData, LookupDataManager},
};

/// The main purpose of this factory is to allow creating a new instance of the
/// [`StdWasmApiImpl`] for each incoming gRPC request, with an immutable
/// snapshot of the current lookup data.
pub struct StdWasmApiFactory<const S: usize> {
    pub lookup_data_manager: Arc<LookupDataManager<S>>,
}

impl<const S: usize> WasmApiFactory for StdWasmApiFactory<S> {
    fn create_wasm_api(&self, request: Vec<u8>, response: Rc<Cell<Vec<u8>>>) -> Box<dyn WasmApi> {
        Box::new(StdWasmApiImpl {
            lookup_data: self.lookup_data_manager.create_lookup_data(),
            logger: Rc::new(StandaloneLogger),
            request,
            response,
        })
    }
}

/// Implementation of the standard Oak Functions API.
///
/// There are probably more locks than necessary here, it should be possible to
/// reduce them in the future.
#[derive(Clone)]
pub struct StdWasmApiImpl<const S: usize> {
    lookup_data: LookupData<S>,
    logger: Rc<dyn OakLogger>,
    /// Current request, as received from the client.
    request: Vec<u8>,
    /// Current response, as received from the Wasm module.
    response: Rc<Cell<Vec<u8>>>,
}

impl<const S: usize> StdWasmApi for StdWasmApiImpl<S> {
    fn read_request(
        &mut self,
        _: ReadRequestRequest,
    ) -> Result<ReadRequestResponse, micro_rpc::Status> {
        self.logger.log_sensitive(Level::Debug, "invoked read_request");
        Ok(ReadRequestResponse { body: self.request.clone() })
    }
    fn write_response(
        &mut self,
        req: WriteResponseRequest,
    ) -> Result<WriteResponseResponse, micro_rpc::Status> {
        self.logger.log_sensitive(Level::Debug, "invoked write_response");
        self.response.set(req.body);

        Ok(WriteResponseResponse::default())
    }

    #[allow(unused_variables)]
    fn log(&mut self, request: LogRequest) -> Result<LogResponse, ::micro_rpc::Status> {
        self.logger.log_sensitive(Level::Debug, "invoked log");
        #[cfg(not(feature = "deny_sensitive_logging"))]
        self.logger.log_sensitive(Level::Debug, &alloc::format!("[Wasm] {}", request.message));
        Ok(LogResponse::default())
    }

    fn lookup_data(
        &mut self,
        request: LookupDataRequest,
    ) -> Result<LookupDataResponse, ::micro_rpc::Status> {
        // The request is the key to lookup.
        let key = request.key;

        #[cfg(not(feature = "deny_sensitive_logging"))]
        {
            let key_to_log = crate::lookup::limit(&key, 512);
            self.logger.log_sensitive(
                Level::Debug,
                &alloc::format!("lookup_data(): key: {}", crate::lookup::format_bytes(key_to_log)),
            );
        }
        let value = self.lookup_data.get(&key);

        // Log found value.
        #[cfg(not(feature = "deny_sensitive_logging"))]
        value.as_ref().map_or_else(
            || {
                self.logger.log_sensitive(Level::Debug, "storage_get_item(): value not found");
            },
            |value| {
                // Truncate value for logging.
                let value_to_log = crate::lookup::limit(value, 512);
                self.logger.log_sensitive(
                    Level::Debug,
                    &alloc::format!(
                        "storage_get_item(): value: {}",
                        crate::lookup::format_bytes(value_to_log)
                    ),
                );
            },
        );

        Ok(LookupDataResponse { value: value.map(Into::into) })
    }

    fn lookup_data_multi(
        &mut self,
        request: LookupDataMultiRequest,
    ) -> Result<LookupDataMultiResponse, ::micro_rpc::Status> {
        // The request contains the keys to lookup.
        let keys = request.keys;

        #[cfg(not(feature = "deny_sensitive_logging"))]
        self.logger.log_sensitive(
            Level::Debug,
            &alloc::format!("lookup_data_multi(): {} keys", keys.len()),
        );

        let values: Vec<BytesValue> = keys
            .iter()
            .map(|key| match self.lookup_data.get(key) {
                Some(value) => BytesValue { found: true, value: value.into() },
                None => BytesValue { found: false, value: Vec::new() },
            })
            .collect();

        Ok(LookupDataMultiResponse { values })
    }

    fn test(&mut self, req: TestRequest) -> Result<TestResponse, micro_rpc::Status> {
        self.logger.log_sensitive(Level::Debug, "invoked test");
        Ok(TestResponse { body: if req.echo { req.body } else { Vec::new() } })
    }
}

impl<const S: usize> WasmApi for StdWasmApiImpl<S> {
    fn transport(&mut self) -> Box<dyn micro_rpc::Transport<Error = !>> {
        Box::new(StdWasmApiServer::new(self.clone()))
    }
}
