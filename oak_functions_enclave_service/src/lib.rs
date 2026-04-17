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

extern crate alloc;

use alloc::{format, string::ToString, sync::Arc, vec::Vec};

use oak_core::sync::OnceCell;
use oak_crypto::encryption_key::EncryptionKeyHandle;
use oak_functions_service::{Handler, Observer, instance::OakFunctionsInstance};
use oak_micro_rpc::oak::functions::OakFunctions;
use oak_proto_rust::oak::functions::{
    AbortNextLookupDataResponse, Empty, ExtendNextLookupDataRequest, ExtendNextLookupDataResponse,
    FinishNextLookupDataRequest, FinishNextLookupDataResponse, InitializeRequest,
    InitializeResponse, InvokeRequest, InvokeResponse, LookupDataChunk, ReserveRequest,
    ReserveResponse, extend_next_lookup_data_request::Data,
};
use oak_restricted_kernel_sdk::{Attester, handler::EncryptionHandler};
use prost::Message;

pub struct OakFunctionsService<EKH, A, H>
where
    EKH: EncryptionKeyHandle + 'static,
    A: Attester,
    H: Handler,
{
    attester: A,
    encryption_key_handle: Arc<EKH>,
    instance_config: H::HandlerConfig,
    instance: OnceCell<OakFunctionsInstance<H>>,
    observer: Option<Arc<dyn Observer + Send + Sync>>,
}

impl<EKH, A, H> OakFunctionsService<EKH, A, H>
where
    EKH: EncryptionKeyHandle + 'static,
    A: Attester,
    H: Handler,
{
    pub fn new(
        attester: A,
        encryption_key_handle: Arc<EKH>,
        observer: Option<Arc<dyn Observer + Send + Sync>>,
        instance_config: H::HandlerConfig,
    ) -> Self {
        Self {
            attester,
            encryption_key_handle,
            instance_config,
            instance: OnceCell::new(),
            observer,
        }
    }
    fn get_instance(&self) -> Result<&OakFunctionsInstance<H>, micro_rpc::Status> {
        self.instance.get().ok_or_else(|| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::FailedPrecondition,
                "not initialized",
            )
        })
    }
}

impl<EKH, A, H> OakFunctions for OakFunctionsService<EKH, A, H>
where
    EKH: EncryptionKeyHandle + 'static,
    A: Attester,
    H: Handler,
{
    fn initialize(
        &self,
        request: InitializeRequest,
    ) -> Result<InitializeResponse, micro_rpc::Status> {
        log::debug!("called initialize (Wasm module size: {} bytes)", request.wasm_module.len());
        match self.instance.get() {
            Some(_) => Err(micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::FailedPrecondition,
                "already initialized",
            )),
            None => {
                let instance = OakFunctionsInstance::new(
                    &request,
                    self.observer.clone(),
                    self.instance_config.clone(),
                )?;
                if self.instance.set(instance).is_err() {
                    return Err(micro_rpc::Status::new_with_message(
                        micro_rpc::StatusCode::FailedPrecondition,
                        "already initialized",
                    ));
                }
                let evidence = self.attester.quote().map_err(|err| {
                    micro_rpc::Status::new_with_message(
                        micro_rpc::StatusCode::Internal,
                        format!("failed to get evidence: {err}"),
                    )
                })?;
                Ok(InitializeResponse { evidence: Some(evidence) })
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
            request.data.as_ref().map_or(0, |data| {
                match data {
                    Data::Chunk(chunk) => chunk.items.len() as isize,
                    Data::LengthDelimitedEntries(_) => -1,
                }
            })
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
        instance.extend_lookup_data_chunk(request)?;
        instance.finish_next_lookup_data(FinishNextLookupDataRequest {})
    }

    fn reserve(&self, request: ReserveRequest) -> Result<ReserveResponse, micro_rpc::Status> {
        self.get_instance()?.reserve(request)
    }
}
