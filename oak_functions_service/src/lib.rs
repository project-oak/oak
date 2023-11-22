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
#![feature(unwrap_infallible)]

extern crate alloc;

#[cfg(test)]
extern crate std;

pub mod proto {
    pub mod oak {
        pub use oak_crypto::proto::oak::crypto;
        pub mod functions {
            #![allow(dead_code)]
            use prost::Message;
            include!(concat!(env!("OUT_DIR"), "/oak.functions.rs"));
        }
    }
}

pub mod instance;
pub mod logger;
pub mod lookup;
pub mod wasm;

use alloc::{format, string::ToString, sync::Arc, vec::Vec};
use instance::OakFunctionsInstance;
use oak_core::sync::OnceCell;
use oak_crypto::encryptor::EncryptionKeyProvider;
use oak_remote_attestation::{
    attester::{AttestationReportGenerator, Attester},
    handler::EncryptionHandler,
};
use prost::Message;
use proto::oak::functions::{
    AbortNextLookupDataResponse, Empty, ExtendNextLookupDataRequest, ExtendNextLookupDataResponse,
    FinishNextLookupDataRequest, FinishNextLookupDataResponse, InitializeRequest,
    InitializeResponse, InvokeRequest, InvokeResponse, OakFunctions, PublicKeyInfo,
};

pub struct OakFunctionsService {
    attestation_report_generator: Arc<dyn AttestationReportGenerator>,
    encryption_key_provider: Arc<EncryptionKeyProvider>,
    instance: OnceCell<OakFunctionsInstance>,
}

impl OakFunctionsService {
    pub fn new(attestation_report_generator: Arc<dyn AttestationReportGenerator>) -> Self {
        Self {
            attestation_report_generator,
            encryption_key_provider: Arc::new(EncryptionKeyProvider::generate()),
            instance: OnceCell::new(),
        }
    }
    fn get_instance(&self) -> Result<&OakFunctionsInstance, micro_rpc::Status> {
        self.instance.get().ok_or_else(|| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::FailedPrecondition,
                "not initialized",
            )
        })
    }
}

impl OakFunctions for OakFunctionsService {
    fn initialize(
        &self,
        request: InitializeRequest,
    ) -> Result<InitializeResponse, micro_rpc::Status> {
        log::debug!(
            "called initialize (Wasm module size: {} bytes)",
            request.wasm_module.len()
        );
        match self.instance.get() {
            Some(_) => Err(micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::FailedPrecondition,
                "already initialized",
            )),
            None => {
                let instance = OakFunctionsInstance::new(&request)?;
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
                if self.instance.set(instance).is_err() {
                    return Err(micro_rpc::Status::new_with_message(
                        micro_rpc::StatusCode::FailedPrecondition,
                        "already initialized",
                    ));
                }
                Ok(InitializeResponse {
                    public_key_info: Some(PublicKeyInfo {
                        public_key: attestation_evidence.encryption_public_key,
                        attestation: attestation_evidence.attestation,
                    }),
                })
            }
        }
    }

    fn handle_user_request(
        &self,
        request: InvokeRequest,
    ) -> Result<InvokeResponse, micro_rpc::Status> {
        log::debug!("called handle_user_request");
        let encryption_key_provider = self.encryption_key_provider.clone();
        let instance = self.get_instance()?;

        let encrypted_request = request.encrypted_request.ok_or_else(|| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::InvalidArgument,
                "InvokeRequest doesn't contain an encrypted request".to_string(),
            )
        })?;

        EncryptionHandler::create(encryption_key_provider, |r| {
            // Wrap the invocation result (which may be an Error) into a micro RPC Response
            // wrapper protobuf, and encode that as bytes.
            let response_result: Result<Vec<u8>, micro_rpc::Status> =
                instance.handle_user_request(r);
            let response: micro_rpc::ResponseWrapper = response_result.into();
            response.encode_to_vec()
        })
        .invoke(&encrypted_request)
        .map(
            #[allow(clippy::needless_update)]
            |encrypted_response| InvokeResponse {
                encrypted_response: Some(encrypted_response),
                ..Default::default()
            },
        )
        .map_err(|err| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                format!("couldn't call handle_user_request handler: {:?}", err),
            )
        })
    }

    fn extend_next_lookup_data(
        &self,
        request: ExtendNextLookupDataRequest,
    ) -> Result<ExtendNextLookupDataResponse, micro_rpc::Status> {
        log::debug!(
            "called extend_next_lookup_data (items: {})",
            request.chunk.as_ref().map(|c| c.items.len()).unwrap_or(0)
        );
        self.get_instance()?.extend_next_lookup_data(request)
    }

    fn finish_next_lookup_data(
        &self,
        request: FinishNextLookupDataRequest,
    ) -> Result<FinishNextLookupDataResponse, micro_rpc::Status> {
        log::debug!("called finish_next_lookup_data");
        self.get_instance()?.finish_next_lookup_data(request)
    }

    fn abort_next_lookup_data(
        &self,
        request: Empty,
    ) -> Result<AbortNextLookupDataResponse, micro_rpc::Status> {
        log::debug!("called abort_next_lookup_data");
        self.get_instance()?.abort_next_lookup_data(request)
    }
}
