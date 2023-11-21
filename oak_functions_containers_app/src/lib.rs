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

use crate::proto::oak::functions::oak_functions_server::{OakFunctions, OakFunctionsServer};
use anyhow::anyhow;
use oak_crypto::encryptor::{AsyncRecipientContextGenerator, EncryptionKeyProvider};
use oak_functions_service::{
    instance::OakFunctionsInstance,
    proto::oak::functions::{
        AbortNextLookupDataResponse, Empty, ExtendNextLookupDataRequest,
        ExtendNextLookupDataResponse, FinishNextLookupDataRequest, FinishNextLookupDataResponse,
        InitializeRequest, InitializeResponse, InvokeRequest, InvokeResponse, PublicKeyInfo,
    },
};
use oak_remote_attestation::{
    attester::{AttestationReportGenerator, Attester},
    handler::AsyncEncryptionHandler,
};
use prost::Message;
use std::sync::{Arc, OnceLock};
use tokio::net::TcpListener;
use tokio_stream::wrappers::TcpListenerStream;

pub mod proto {
    pub mod oak {
        pub mod functions {
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.functions");
        }
        pub mod containers {
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.containers");
        }
        pub use oak_crypto::proto::oak::crypto;
        pub use oak_remote_attestation::proto::oak::{attestation, session};
    }
}

pub mod orchestrator_client;

// Instance of the OakFunctions service for Oak Containers.
pub struct OakFunctionsContainersService<G: AsyncRecipientContextGenerator + Send + Sync> {
    attestation_report_generator: Arc<dyn AttestationReportGenerator>,
    encryption_key_provider: Arc<EncryptionKeyProvider>,
    instance: OnceLock<Arc<OakFunctionsInstance>>,
    orchestrator_client: Arc<G>,
}

impl<G: AsyncRecipientContextGenerator + Send + Sync> OakFunctionsContainersService<G> {
    pub fn new(
        attestation_report_generator: Arc<dyn AttestationReportGenerator>,
        orchestrator_client: Arc<G>,
    ) -> Self {
        Self {
            attestation_report_generator,
            encryption_key_provider: Arc::new(EncryptionKeyProvider::generate()),
            instance: OnceLock::new(),
            orchestrator_client,
        }
    }

    fn get_instance(&self) -> Result<Arc<OakFunctionsInstance>, tonic::Status> {
        self.instance
            .get()
            .cloned()
            .ok_or_else(|| tonic::Status::failed_precondition("not initialized"))
    }
}

fn map_status(status: micro_rpc::Status) -> tonic::Status {
    let code = match status.code {
        micro_rpc::StatusCode::Ok => tonic::Code::Ok,
        micro_rpc::StatusCode::Cancelled => tonic::Code::Cancelled,
        micro_rpc::StatusCode::Unknown => tonic::Code::Unknown,
        micro_rpc::StatusCode::InvalidArgument => tonic::Code::InvalidArgument,
        micro_rpc::StatusCode::DeadlineExceeded => tonic::Code::DeadlineExceeded,
        micro_rpc::StatusCode::NotFound => tonic::Code::NotFound,
        micro_rpc::StatusCode::AlreadyExists => tonic::Code::AlreadyExists,
        micro_rpc::StatusCode::PermissionDenied => tonic::Code::PermissionDenied,
        micro_rpc::StatusCode::ResourceExhausted => tonic::Code::ResourceExhausted,
        micro_rpc::StatusCode::FailedPrecondition => tonic::Code::FailedPrecondition,
        micro_rpc::StatusCode::Aborted => tonic::Code::Aborted,
        micro_rpc::StatusCode::OutOfRange => tonic::Code::OutOfRange,
        micro_rpc::StatusCode::Unimplemented => tonic::Code::Unimplemented,
        micro_rpc::StatusCode::Internal => tonic::Code::Internal,
        micro_rpc::StatusCode::Unavailable => tonic::Code::Unavailable,
        micro_rpc::StatusCode::DataLoss => tonic::Code::DataLoss,
        micro_rpc::StatusCode::Unauthenticated => tonic::Code::Unauthenticated,
    };
    tonic::Status::new(code, status.message)
}

#[tonic::async_trait]
impl<G: AsyncRecipientContextGenerator + Send + Sync + 'static> OakFunctions
    for OakFunctionsContainersService<G>
{
    async fn initialize(
        &self,
        request: tonic::Request<InitializeRequest>,
    ) -> Result<tonic::Response<InitializeResponse>, tonic::Status> {
        let request = request.into_inner();
        match self.instance.get() {
            Some(_) => Err(tonic::Status::failed_precondition("already initialized")),
            None => {
                let instance = Arc::new(OakFunctionsInstance::new(&request).map_err(map_status)?);
                let attester = Attester::new(
                    self.attestation_report_generator.clone(),
                    self.encryption_key_provider.clone(),
                );
                let attestation_evidence =
                    attester.generate_attestation_evidence().map_err(|err| {
                        tonic::Status::internal(format!(
                            "couldn't get attestation evidence: {:?}",
                            err
                        ))
                    })?;
                if self.instance.set(instance).is_err() {
                    return Err(tonic::Status::failed_precondition("already initialized"));
                }
                Ok(tonic::Response::new(InitializeResponse {
                    public_key_info: Some(PublicKeyInfo {
                        public_key: attestation_evidence.encryption_public_key,
                        attestation: attestation_evidence.attestation,
                    }),
                }))
            }
        }
    }

    async fn handle_user_request(
        &self,
        request: tonic::Request<InvokeRequest>,
    ) -> Result<tonic::Response<InvokeResponse>, tonic::Status> {
        let encryption_key_provider = self.orchestrator_client.clone();
        let instance = self.get_instance()?;

        let encrypted_request = request.into_inner().encrypted_request.ok_or_else(|| {
            tonic::Status::invalid_argument(
                "InvokeRequest doesn't contain an encrypted request".to_string(),
            )
        })?;

        AsyncEncryptionHandler::create(encryption_key_provider, |r| {
            // Wrap the invocation result (which may be an Error) into a micro RPC Response
            // wrapper protobuf, and encode that as bytes.
            let response_result: Result<Vec<u8>, micro_rpc::Status> =
                instance.handle_user_request(r);
            let response: micro_rpc::ResponseWrapper = response_result.into();
            response.encode_to_vec()
        })
        .invoke(&encrypted_request)
        .await
        .map(
            #[allow(clippy::needless_update)]
            |encrypted_response| {
                tonic::Response::new(InvokeResponse {
                    encrypted_response: Some(encrypted_response),
                    ..Default::default()
                })
            },
        )
        .map_err(|err| {
            tonic::Status::internal(format!(
                "couldn't call handle_user_request handler: {:?}",
                err
            ))
        })
    }

    async fn extend_next_lookup_data(
        &self,
        request: tonic::Request<ExtendNextLookupDataRequest>,
    ) -> Result<tonic::Response<ExtendNextLookupDataResponse>, tonic::Status> {
        self.get_instance()?
            .extend_next_lookup_data(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }

    async fn finish_next_lookup_data(
        &self,
        request: tonic::Request<FinishNextLookupDataRequest>,
    ) -> Result<tonic::Response<FinishNextLookupDataResponse>, tonic::Status> {
        self.get_instance()?
            .finish_next_lookup_data(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }

    async fn abort_next_lookup_data(
        &self,
        request: tonic::Request<Empty>,
    ) -> Result<tonic::Response<AbortNextLookupDataResponse>, tonic::Status> {
        self.get_instance()?
            .abort_next_lookup_data(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }
}

// Starts up and serves an OakFunctionsContainersService instance from the provided TCP listener.
pub async fn serve<G: AsyncRecipientContextGenerator + Send + Sync + 'static>(
    listener: TcpListener,
    attestation_report_generator: Arc<dyn AttestationReportGenerator>,
    orchestrator_client: Arc<G>,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(OakFunctionsServer::new(OakFunctionsContainersService::new(
            attestation_report_generator,
            orchestrator_client,
        )))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("starting up the service failed with error: {:?}", error))
}
