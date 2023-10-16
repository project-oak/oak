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
use alloc::{format, sync::Arc, vec::Vec};
use anyhow::Context;
use oak_crypto::encryptor::EncryptionKeyProvider;
use oak_remote_attestation::{
    attester::{AttestationReportGenerator, Attester},
    handler::EncryptionHandler,
};
use prost::Message;

struct OakIreeInstance {
    iree_model: iree::IreeModel,
}

impl OakIreeInstance {
    fn invoke(&mut self, request: &[u8]) -> Result<Vec<u8>, micro_rpc::Status> {
        self.iree_model
            .run(request)
            .context("couldn't run IREE inference")
            .map_err(|err| {
                micro_rpc::Status::new_with_message(
                    micro_rpc::StatusCode::Internal,
                    format!("couldn't handle invoke: {:?}", err),
                )
            })
    }
}

pub struct IreeService {
    attestation_report_generator: Arc<dyn AttestationReportGenerator>,
    encryption_key_provider: Arc<EncryptionKeyProvider>,
    instance: Option<OakIreeInstance>,
}

impl IreeService {
    pub fn new(attestation_report_generator: Arc<dyn AttestationReportGenerator>) -> Self {
        Self {
            attestation_report_generator,
            encryption_key_provider: Arc::new(EncryptionKeyProvider::new()),
            instance: None,
        }
    }
    fn get_instance(&mut self) -> Result<&mut OakIreeInstance, micro_rpc::Status> {
        self.instance.as_mut().ok_or_else(|| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::FailedPrecondition,
                "not initialized",
            )
        })
    }
}

impl Iree for IreeService {
    fn initialize(
        &mut self,
        _initialization: InitializeRequest,
    ) -> Result<InitializeResponse, micro_rpc::Status> {
        match &mut self.instance {
            Some(_) => Err(micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::FailedPrecondition,
                "already initialized",
            )),
            None => {
                let instance = {
                    let mut iree_model = iree::IreeModel::new();
                    iree_model
                        .initialize()
                        .map_err(|_err| micro_rpc::Status::new(micro_rpc::StatusCode::Internal))?;
                    OakIreeInstance { iree_model }
                };
                let attester = Attester::new(
                    self.attestation_report_generator.clone(),
                    self.encryption_key_provider.clone(),
                );
                let attestation_evidence =
                    attester.generate_attestation_evidence().map_err(|err| {
                        micro_rpc::Status::new_with_message(
                            micro_rpc::StatusCode::Internal,
                            format!("couldn't get attestation evidence: {:?}", err),
                        )
                    })?;
                self.instance = Some(instance);
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
        let encryption_key_provider = self.encryption_key_provider.clone();
        let instance = self.get_instance()?;
        EncryptionHandler::create(encryption_key_provider, |r| {
            let response: micro_rpc::ResponseWrapper = instance.invoke(&r).into();
            response.encode_to_vec()
        })
        .invoke(&request_message.body)
        .map(|response| InvokeResponse { body: response })
        .map_err(|err| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                format!("couldn't invoke handler: {:?}", err),
            )
        })
    }
}
