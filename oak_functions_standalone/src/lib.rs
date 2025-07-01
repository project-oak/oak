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

#![feature(c_size_t)]

use std::{error::Error, pin::Pin, sync::Arc};

use anyhow::Context;
use oak_functions_service::{instance::OakFunctionsInstance, Handler};
use oak_grpc::oak::functions::standalone::oak_functions_session_server::{
    OakFunctionsSession, OakFunctionsSessionServer,
};
use oak_proto_rust::oak::functions::{
    standalone::{OakSessionRequest, OakSessionResponse},
    ExtendNextLookupDataRequest, ExtendNextLookupDataResponse, FinishNextLookupDataRequest,
    FinishNextLookupDataResponse, InitializeRequest, ReserveRequest, ReserveResponse,
};
use oak_session::{
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    ServerSession, Session,
};
use tokio::io::{AsyncRead, AsyncWrite};
use tokio_stream::{Stream, StreamExt};
use tonic::{codec::CompressionEncoding, transport::server::Connected};

// Arguements to start up the Oak Functions Session Service.
// While currently there is only one argument, in the future lookup data
// arguments will be added.
pub struct OakFunctionsSessionArgs {
    pub wasm_initialization: InitializeRequest,
}

// Instance of the OakFunctions service for Oak Containers.
pub struct OakFunctionsSessionService<H: Handler> {
    instance: Arc<OakFunctionsInstance<H>>,
}

impl<H: Handler> OakFunctionsSessionService<H> {
    pub fn startup(
        instance_config: H::HandlerConfig,
        oak_functions_session_args: OakFunctionsSessionArgs,
    ) -> Self {
        let instance = OakFunctionsInstance::new(
            &oak_functions_session_args.wasm_initialization,
            None,
            instance_config.clone(),
        )
        .map_err(map_status)
        .unwrap();

        // TODO: b/424407998 - Load lookup data via calls to `reserve`,
        // `finish_next_lookup_data`, and `extend_next_lookup_data`.
        Self { instance: Arc::new(instance) }
    }

    pub fn extend_next_lookup_data(
        &self,
        request: ExtendNextLookupDataRequest,
    ) -> tonic::Result<ExtendNextLookupDataResponse> {
        self.get_instance().extend_next_lookup_data(request).map_err(map_status)
    }

    pub fn finish_next_lookup_data(
        &self,
        request: FinishNextLookupDataRequest,
    ) -> tonic::Result<FinishNextLookupDataResponse> {
        self.get_instance().finish_next_lookup_data(request).map_err(map_status)
    }

    pub fn reserve(&self, request: ReserveRequest) -> tonic::Result<ReserveResponse> {
        self.get_instance().reserve(request).map_err(map_status)
    }

    #[allow(clippy::result_large_err)]
    fn get_instance(&self) -> Arc<OakFunctionsInstance<H>> {
        self.instance.clone()
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
impl<H> OakFunctionsSession for OakFunctionsSessionService<H>
where
    H: Handler + 'static,
    H::HandlerType: Send + Sync,
{
    type OakSessionStream =
        Pin<Box<dyn Stream<Item = Result<OakSessionResponse, tonic::Status>> + Send + 'static>>;

    async fn oak_session(
        &self,
        request: tonic::Request<tonic::Streaming<OakSessionRequest>>,
    ) -> Result<tonic::Response<Self::OakSessionStream>, tonic::Status> {
        let mut server_session: ServerSession = ServerSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .map_err(|e| tonic::Status::internal(format!("could not create server session: {e:?}")))?;

        let instance: Arc<OakFunctionsInstance<H>> = self.get_instance();

        let mut request_stream = request.into_inner();
        let response_stream = async_stream::try_stream! {
          while let Some(result_request) = request_stream.next().await {
            let oak_session_request = result_request?;
            let session_request = oak_session_request
              .request
              .ok_or(tonic::Status::invalid_argument("No request in OakSessionRequest"))?;
            if server_session.is_open() {
              let decrypted_request = server_session.decrypt(session_request).map_err(|e| tonic::Status::internal(format!("{e:?}")))?;

              let invoke_response =
                instance.handle_user_request(decrypted_request).map_err(map_status);

              let session_response = server_session.encrypt(invoke_response.unwrap()).map_err(|e| tonic::Status::internal(format!("{e:?}")))?;

              let oak_session_response = OakSessionResponse {
                response: Some(session_response),
              };

              yield oak_session_response;

            } else {
              server_session.handle_init_message(session_request).map_err(|e| tonic::Status::internal(format!("{e:?}")))?;
              if !server_session.is_open() {
                let session_response = server_session.next_init_message().map_err(|e| tonic::Status::internal(format!("{e:?}")))?;
                let oak_session_response = OakSessionResponse {
                  response: Some(session_response),
                };
                yield oak_session_response;
              }
            }
          }
        };
        Ok(tonic::Response::new(Box::pin(response_stream) as Self::OakSessionStream))
    }
}

// Equivalent to `tonic::status::GRPC_STATUS_HEADER_CODE`.
// We're not sending traffic over a "real" network anyway, after all.
const MAX_DECODING_MESSAGE_SIZE: usize = 1024 * 1024 * 1024;

/// Starts up and serves an OakFunctionsStandaloneService instance from the
/// provided stream of connections.
// The type of the stream is pretty horrible; we can define a slightly cleaner
// type aliases for it when `type_alias_impl_trait` has been stabilized; see https://github.com/rust-lang/rust/issues/63063.
pub async fn serve<H>(
    stream: Box<
        dyn tokio_stream::Stream<
                Item = Result<
                    impl Connected + AsyncRead + AsyncWrite + Send + Unpin + 'static,
                    impl Error + Send + Sync + 'static,
                >,
            > + Send
            + Unpin,
    >,
    handler_config: H::HandlerConfig,
    oak_functions_session_args: OakFunctionsSessionArgs,
) -> anyhow::Result<()>
where
    H: Handler + 'static,
    H::HandlerType: Send + Sync,
{
    tonic::transport::Server::builder()
        .layer(tower::load_shed::LoadShedLayer::new())
        .add_service(
            OakFunctionsSessionServer::new(OakFunctionsSessionService::<H>::startup(
                handler_config,
                oak_functions_session_args,
            ))
            .max_decoding_message_size(MAX_DECODING_MESSAGE_SIZE)
            .accept_compressed(CompressionEncoding::Gzip),
        )
        .add_service(oak_debug_service::Service::new_server())
        .serve_with_incoming(stream)
        .await
        .context("failed to start up the service")
}
