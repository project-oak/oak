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

#![no_std]
#![feature(never_type)]

extern crate alloc;

pub mod proto {
    pub mod oak {
        pub mod iree {
            #![allow(dead_code)]
            use prost::Message;
            include!(concat!(env!("OUT_DIR"), "/oak.iree.rs"));
        }
    }
}
mod iree;

use crate::proto::oak::iree::{
    AttestationEvidence, InitializeRequest, InitializeResponse, InvokeRequest, InvokeResponse, Iree,
};
use alloc::{boxed::Box, format, sync::Arc, vec::Vec};
use anyhow::Context;
use oak_remote_attestation::{
    attester::AttestationReportGenerator,
    handler::{AttestationHandler, AttestationSessionHandler},
};

struct IreeHandler {
    iree_model: iree::IreeModel,
}

impl micro_rpc::Transport for IreeHandler {
    type Error = anyhow::Error;
    fn invoke(&mut self, request: &[u8]) -> anyhow::Result<Vec<u8>> {
        self.iree_model
            .run(request)
            .context("couldn't run IREE inference")
    }
}

enum InitializationState {
    Uninitialized,
    Initialized(Box<dyn AttestationHandler>),
}

pub struct IreeService {
    attestation_report_generator: Arc<dyn AttestationReportGenerator>,
    initialization_state: InitializationState,
}

impl IreeService {
    pub fn new(attestation_report_generator: Arc<dyn AttestationReportGenerator>) -> Self {
        Self {
            attestation_report_generator,
            initialization_state: InitializationState::Uninitialized,
        }
    }
}

impl Iree for IreeService {
    fn initialize(
        &mut self,
        _initialization: InitializeRequest,
    ) -> Result<InitializeResponse, micro_rpc::Status> {
        match &mut self.initialization_state {
            InitializationState::Initialized(_attestation_handler) => {
                Err(micro_rpc::Status::new_with_message(
                    micro_rpc::StatusCode::FailedPrecondition,
                    "already initialized",
                ))
            }
            InitializationState::Uninitialized => {
                let mut iree_model = iree::IreeModel::new();
                iree_model
                    .initialize()
                    .map_err(|_err| micro_rpc::Status::new(micro_rpc::StatusCode::Internal))?;

                let attestation_handler = Box::new(
                    AttestationSessionHandler::create(
                        self.attestation_report_generator.clone(),
                        IreeHandler { iree_model },
                    )
                    .map_err(|err| {
                        micro_rpc::Status::new_with_message(
                            micro_rpc::StatusCode::Internal,
                            format!("couldn't create attestation handler: {:?}", err),
                        )
                    })?,
                );
                let attestation_evidence =
                    attestation_handler
                        .get_attestation_evidence()
                        .map_err(|err| {
                            micro_rpc::Status::new_with_message(
                                micro_rpc::StatusCode::Internal,
                                format!("couldn't get attestation evidence: {:?}", err),
                            )
                        })?;
                self.initialization_state = InitializationState::Initialized(attestation_handler);

                Ok(InitializeResponse {
                    attestation_evidence: Some(AttestationEvidence {
                        attestation_report: attestation_evidence.attestation,
                        public_key: attestation_evidence.encryption_public_key,
                    }),
                })
            }
        }
    }

    fn invoke(
        &mut self,
        request_message: InvokeRequest,
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
}
