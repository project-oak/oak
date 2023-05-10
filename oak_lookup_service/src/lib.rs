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

#![no_std]
#![feature(never_type)]

extern crate alloc;

mod logger;
mod remote_attestation;

use crate::remote_attestation::{AttestationHandler, AttestationSessionHandler};
use alloc::{boxed::Box, format, sync::Arc};
use oak_functions_lookup::{LookupData, LookupDataManager};
use oak_functions_service::proto::oak::functions::{
    AbortNextLookupDataResponse, Empty, ExtendNextLookupDataRequest, ExtendNextLookupDataResponse,
    FinishNextLookupDataRequest, FinishNextLookupDataResponse, InitializeRequest,
    InitializeResponse, InvokeRequest, InvokeResponse, LookupDataChunk, OakFunctions,
    PublicKeyInfo,
};
use oak_remote_attestation_interactive::handshaker::AttestationGenerator;

pub use crate::logger::StandaloneLogger;

enum InitializationState {
    Uninitialized,
    Initialized(Box<dyn AttestationHandler>),
}

pub struct LookupService {
    attestation_generator: Arc<dyn AttestationGenerator>,
    initialization_state: InitializationState,
    lookup_data_manager: Arc<LookupDataManager<logger::StandaloneLogger>>,
}

impl LookupService {
    pub fn new(attestation_generator: Arc<dyn AttestationGenerator>) -> Self {
        Self {
            attestation_generator,
            initialization_state: InitializationState::Uninitialized,
            lookup_data_manager: Arc::new(
                LookupDataManager::new_empty(StandaloneLogger::default()),
            ),
        }
    }
}

struct LookupHandler {
    lookup_data: Arc<LookupDataManager<logger::StandaloneLogger>>,
}

impl LookupHandler {
    fn new(lookup_data: Arc<LookupDataManager<logger::StandaloneLogger>>) -> Self {
        Self { lookup_data }
    }
}

impl micro_rpc::Transport for LookupHandler {
    type Error = anyhow::Error;
    fn invoke(&mut self, request_bytes: &[u8]) -> Result<micro_rpc::Vec<u8>, Self::Error> {
        let lookup_data = self.lookup_data.create_lookup_data();
        Ok(lookup_data
            .get(request_bytes)
            .unwrap_or_default())
    }
}

impl OakFunctions for LookupService {
    fn initialize(
        &mut self,
        _initialization: &InitializeRequest,
    ) -> Result<InitializeResponse, micro_rpc::Status> {
        match &mut self.initialization_state {
            InitializationState::Initialized(_attestation_handler) => {
                Err(micro_rpc::Status::new_with_message(
                    micro_rpc::StatusCode::FailedPrecondition,
                    "already initialized",
                ))
            }
            InitializationState::Uninitialized => {
                // TODO(#3442): Implement constant response size policy.
                let lookup_handler =
                    LookupHandler::new(self.lookup_data_manager.clone());
                let attestation_handler = Box::new(
                    AttestationSessionHandler::create(
                        self.attestation_generator.clone(),
                        lookup_handler,
                    )
                    .map_err(|err| {
                        micro_rpc::Status::new_with_message(
                            micro_rpc::StatusCode::Internal,
                            format!("couldn't create attestation handler: {:?}", err),
                        )
                    })?,
                );
                let public_key_info = attestation_handler.get_public_key_info();
                self.initialization_state = InitializationState::Initialized(attestation_handler);
                Ok(InitializeResponse {
                    public_key_info: Some(PublicKeyInfo {
                        public_key: public_key_info.public_key,
                        attestation: public_key_info.attestation,
                    }),
                })
            }
        }
    }

    fn invoke(
        &mut self,
        request_message: &InvokeRequest,
    ) -> Result<InvokeResponse, micro_rpc::Status> {
        match &mut self.initialization_state {
            InitializationState::Uninitialized => Err(micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::FailedPrecondition,
                "not initialized",
            )),
            InitializationState::Initialized(attestation_handler) => {
                let response =
                    attestation_handler
                        .invoke(&request_message.body)
                        .map_err(|err| {
                            micro_rpc::Status::new_with_message(
                                micro_rpc::StatusCode::Internal,
                                format!("{:?}", err),
                            )
                        })?;
                Ok(InvokeResponse { body: response })
            }
        }
    }

    fn extend_next_lookup_data(
        &mut self,
        request: &ExtendNextLookupDataRequest,
    ) -> Result<ExtendNextLookupDataResponse, micro_rpc::Status> {
        log::warn!("extend lookup data");
        self.lookup_data_manager
            .extend_next_lookup_data(to_data(&request.chunk));
        Ok(ExtendNextLookupDataResponse {})
    }

    fn finish_next_lookup_data(
        &mut self,
        _request: &FinishNextLookupDataRequest,
    ) -> Result<FinishNextLookupDataResponse, micro_rpc::Status> {
        log::warn!("finish lookup data");
        self.lookup_data_manager.finish_next_lookup_data();
        Ok(FinishNextLookupDataResponse {})
    }

    fn abort_next_lookup_data(
        &mut self,
        _request: &Empty,
    ) -> Result<AbortNextLookupDataResponse, micro_rpc::Status> {
        self.lookup_data_manager.abort_next_lookup_data();
        Ok(AbortNextLookupDataResponse {})
    }
}

// Helper function to convert LookupDataChunk to Data.
// TODO(#3791): Check if we really have to copy here.
fn to_data(chunk: &Option<LookupDataChunk>) -> oak_functions_lookup::Data {
    chunk
        .as_ref()
        .unwrap()
        .items
        .iter()
        .map(|entry| (entry.key.clone(), entry.value.clone()))
        .collect()
}
