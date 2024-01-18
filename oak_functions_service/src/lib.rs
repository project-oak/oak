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

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(never_type)]
#![feature(unwrap_infallible)]
// Required for enabling benchmark tests.
#![feature(test)]

extern crate alloc;

#[cfg(test)]
extern crate std;

pub mod proto {
    pub mod oak {
        pub use oak_attestation::proto::oak::attestation;
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
use oak_attestation::handler::EncryptionHandler;
use oak_core::sync::OnceCell;
use oak_crypto::encryptor::EncryptionKeyHandle;
use prost::Message;
use proto::oak::functions::{
    AbortNextLookupDataResponse, Empty, ExtendNextLookupDataRequest, ExtendNextLookupDataResponse,
    FinishNextLookupDataRequest, FinishNextLookupDataResponse, InitializeRequest,
    InitializeResponse, InvokeRequest, InvokeResponse, LookupDataChunk, OakFunctions,
    PublicKeyInfo, ReserveRequest, ReserveResponse,
};

pub trait Observer {
    fn wasm_initialization(&self, duration: core::time::Duration);
    fn wasm_invocation(&self, duration: core::time::Duration);
}

pub struct OakFunctionsService<
    EKH: EncryptionKeyHandle + 'static,
    EP: oak_restricted_kernel_sdk::EvidenceProvider,
> {
    evidence_provider: EP,
    encryption_key_handle: Arc<EKH>,
    instance: OnceCell<OakFunctionsInstance>,
    observer: Option<Arc<dyn Observer + Send + Sync>>,
}

impl<EKH: EncryptionKeyHandle + 'static, EP: oak_restricted_kernel_sdk::EvidenceProvider>
    OakFunctionsService<EKH, EP>
{
    pub fn new(
        evidence_provider: EP,
        encryption_key_handle: Arc<EKH>,
        observer: Option<Arc<dyn Observer + Send + Sync>>,
    ) -> Self {
        Self {
            evidence_provider,
            encryption_key_handle,
            instance: OnceCell::new(),
            observer,
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
    /// Extract the public key without verifying. This function is intended as a temporary
    /// fix to allow the application to start using the oak SDK, while it still
    /// requires the ability to extract the attestation public key, and to send it
    /// directly to the client.
    // TODO(#4571): Remove this function once the client has been updated to use
    // the verification library. At this point the evidence will just be directly
    // sent to the client, which extracts the public key from it upon succesful
    // verification.
    fn get_encryption_public_key(&self) -> Result<Vec<u8>, anyhow::Error> {
        let encryption_claims = self
            .evidence_provider
            .get_evidence()
            .application_keys
            .claims()
            .map_err(anyhow::Error::msg)?;
        let encryption_cose_key =
            oak_dice::cert::get_public_key_from_claims_set(&encryption_claims)
                .map_err(anyhow::Error::msg)?;
        oak_dice::cert::cose_key_to_hpke_public_key(&encryption_cose_key)
            .map_err(anyhow::Error::msg)
    }
}

impl<EKH: EncryptionKeyHandle + 'static, EP: oak_restricted_kernel_sdk::EvidenceProvider>
    OakFunctions for OakFunctionsService<EKH, EP>
{
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
                let instance = OakFunctionsInstance::new(&request, self.observer.clone())?;
                if self.instance.set(instance).is_err() {
                    return Err(micro_rpc::Status::new_with_message(
                        micro_rpc::StatusCode::FailedPrecondition,
                        "already initialized",
                    ));
                }
                let public_key = self.get_encryption_public_key().map_err(|err| {
                    micro_rpc::Status::new_with_message(
                        micro_rpc::StatusCode::Internal,
                        format!("failed to get encryption public key: {err}"),
                    )
                })?;
                let evidence = oak_attestation::proto::oak::attestation::v1::Evidence::try_from(
                    self.evidence_provider.get_evidence().clone(),
                )
                .map_err(|err| {
                    micro_rpc::Status::new_with_message(
                        micro_rpc::StatusCode::Internal,
                        format!("failed to convert evidence to proto: {err}"),
                    )
                })?;
                #[allow(deprecated)]
                Ok(InitializeResponse {
                    public_key_info: Some(PublicKeyInfo {
                        attestation: Vec::new(),
                        public_key,
                    }),
                    evidence: Some(evidence),
                })
            }
        }
    }

    fn handle_user_request(
        &self,
        request: InvokeRequest,
    ) -> Result<InvokeResponse, micro_rpc::Status> {
        log::debug!("called handle_user_request");
        let encryption_key_handle = self.encryption_key_handle.clone();
        let instance = self.get_instance()?;

        let encrypted_request = request.encrypted_request.ok_or_else(|| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::InvalidArgument,
                "InvokeRequest doesn't contain an encrypted request".to_string(),
            )
        })?;

        EncryptionHandler::create(encryption_key_handle, |r| {
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

    fn stream_lookup_data(
        &self,
        request: LookupDataChunk,
    ) -> Result<FinishNextLookupDataResponse, micro_rpc::Status> {
        let instance = self.get_instance()?;
        instance.extend_lookup_data_chunk(request);
        instance.finish_next_lookup_data(FinishNextLookupDataRequest {})
    }

    fn reserve(&self, request: ReserveRequest) -> Result<ReserveResponse, micro_rpc::Status> {
        self.get_instance()?.reserve(request)
    }
}
