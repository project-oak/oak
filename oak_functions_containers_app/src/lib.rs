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

use std::{
    error::Error,
    sync::{Arc, OnceLock},
};

use anyhow::Context;
use oak_containers_agent::metrics::OakObserver;
use oak_crypto::{encryption_key::AsyncEncryptionKeyHandle, encryptor::ServerEncryptor};
use oak_functions_service::{instance::OakFunctionsInstance, Handler, Observer};
use oak_grpc::oak::functions::oak_functions_server::{OakFunctions, OakFunctionsServer};
use oak_proto_rust::oak::functions::{
    AbortNextLookupDataResponse, Empty, ExtendNextLookupDataRequest, ExtendNextLookupDataResponse,
    FinishNextLookupDataRequest, FinishNextLookupDataResponse, InitializeRequest,
    InitializeResponse, InvokeRequest, InvokeResponse, LookupDataChunk, ReserveRequest,
    ReserveResponse,
};
use opentelemetry::metrics::{Histogram, Meter};
use prost::Message;
use tokio::io::{AsyncRead, AsyncWrite};
use tokio_stream::StreamExt;
use tonic::{codec::CompressionEncoding, transport::server::Connected};
use tracing::Span;

// Instance of the OakFunctions service for Oak Containers.
pub struct OakFunctionsContainersService<H: Handler> {
    instance_config: H::HandlerConfig,
    instance: OnceLock<OakFunctionsInstance<H>>,
    encryption_key_handle: Arc<dyn AsyncEncryptionKeyHandle + Send + Sync>,
    observer: Option<Arc<dyn Observer + Send + Sync>>,
}

impl<H: Handler> OakFunctionsContainersService<H> {
    pub fn new(
        instance_config: H::HandlerConfig,
        encryption_key_handle: Arc<dyn AsyncEncryptionKeyHandle + Send + Sync>,
        observer: Option<Arc<dyn Observer + Send + Sync>>,
    ) -> Self {
        Self { instance_config, instance: OnceLock::new(), encryption_key_handle, observer }
    }

    #[allow(clippy::result_large_err)]
    fn get_instance(&self) -> tonic::Result<&OakFunctionsInstance<H>> {
        self.instance.get().ok_or_else(|| tonic::Status::failed_precondition("not initialized"))
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
impl<H> OakFunctions for OakFunctionsContainersService<H>
where
    H: Handler + 'static,
    H::HandlerType: Send + Sync,
{
    async fn initialize(
        &self,
        request: tonic::Request<InitializeRequest>,
    ) -> tonic::Result<tonic::Response<InitializeResponse>> {
        let request = request.into_inner();
        match self.instance.get() {
            Some(_) => Err(tonic::Status::failed_precondition("already initialized")),
            None => {
                let instance = OakFunctionsInstance::new(
                    &request,
                    self.observer.clone(),
                    self.instance_config.clone(),
                )
                .map_err(map_status)?;
                if self.instance.set(instance).is_err() {
                    return Err(tonic::Status::failed_precondition("already initialized"));
                }
                Ok(tonic::Response::new(InitializeResponse::default()))
            }
        }
    }

    async fn handle_user_request(
        &self,
        request: tonic::Request<InvokeRequest>,
    ) -> tonic::Result<tonic::Response<InvokeResponse>> {
        let instance = self.get_instance()?;

        let encrypted_request = request.into_inner().encrypted_request.ok_or_else(|| {
            tonic::Status::invalid_argument(
                "InvokeRequest doesn't contain an encrypted request".to_string(),
            )
        })?;

        let (server_encryptor, request, _associated_data) =
            ServerEncryptor::decrypt_async(&encrypted_request, self.encryption_key_handle.as_ref())
                .await
                .map_err(|err| {
                    tonic::Status::internal(format!("couldn't decrypt request: {err:?}"))
                })?;

        let response_result: Result<Vec<u8>, micro_rpc::Status> =
            instance.handle_user_request(request);
        let response: micro_rpc::ResponseWrapper = response_result.into();
        let response_vec = response.encode_to_vec();

        // Encrypt and serialize response.
        // The resulting decryptor for consequent requests is discarded because we don't
        // expect another message from the stream.
        let encrypted_response =
            server_encryptor.encrypt(&response_vec, oak_crypto::EMPTY_ASSOCIATED_DATA).map_err(
                |err| tonic::Status::internal(format!("couldn't encrypt resposne: {err:?}")),
            )?;

        Ok(tonic::Response::new(InvokeResponse { encrypted_response: Some(encrypted_response) }))
    }

    async fn extend_next_lookup_data(
        &self,
        request: tonic::Request<ExtendNextLookupDataRequest>,
    ) -> tonic::Result<tonic::Response<ExtendNextLookupDataResponse>> {
        self.get_instance()?
            .extend_next_lookup_data(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }

    async fn finish_next_lookup_data(
        &self,
        request: tonic::Request<FinishNextLookupDataRequest>,
    ) -> tonic::Result<tonic::Response<FinishNextLookupDataResponse>> {
        self.get_instance()?
            .finish_next_lookup_data(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }

    async fn abort_next_lookup_data(
        &self,
        request: tonic::Request<Empty>,
    ) -> tonic::Result<tonic::Response<AbortNextLookupDataResponse>> {
        self.get_instance()?
            .abort_next_lookup_data(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }

    async fn stream_lookup_data(
        &self,
        request: tonic::Request<tonic::Streaming<LookupDataChunk>>,
    ) -> tonic::Result<tonic::Response<FinishNextLookupDataResponse>> {
        let mut request = request.into_inner();

        let instance = self.get_instance()?;
        while let Some(chunk) = request.next().await {
            instance.extend_lookup_data_chunk(chunk?).map_err(map_status)?;
        }
        instance
            .finish_next_lookup_data(FinishNextLookupDataRequest {})
            .map(tonic::Response::new)
            .map_err(map_status)
    }

    async fn reserve(
        &self,
        request: tonic::Request<ReserveRequest>,
    ) -> tonic::Result<tonic::Response<ReserveResponse>> {
        let request = request.into_inner();
        self.get_instance()?.reserve(request).map(tonic::Response::new).map_err(map_status)
    }
}

/// Creates a `trace::Span` for the currently active gRPC request.
///
/// The fields of the Span are filled out according to the OpenTelemetry
/// specifications, if possible.
fn create_trace<Body>(request: &http::Request<Body>) -> Span {
    let uri = request.uri();
    // The general format of a gRPC URI is `http://[::1]:1234/Foo/Bar``, where `Foo` is the service, and `Bar` is the method.
    let mut parts = uri.path().rsplitn(3, '/');
    let method = parts.next();
    let service = parts.next();

    // See https://opentelemetry.io/docs/specs/semconv/rpc/rpc-spans/ and
    // https://opentelemetry.io/docs/specs/semconv/rpc/grpc/ for specifications on what OpenTelemetry
    // expects the traces to look like. Unfortunately the OTel conventions say that
    // the span name must be the full RPC method name, but Rust tracing wants
    // the name to be static, so we'll need to figure something out in the
    // future.
    tracing::info_span!(
        "request",
        rpc.method = method,
        rpc.service = service,
        rpc.system = "grpc",
        rpc.grpc.status_code = tracing::field::Empty,
        server.address = uri.host(),
        server.port = uri.port_u16()
    )
}

struct OtelObserver {
    wasm_initialization: Histogram<u64>,
    wasm_invocation: Histogram<u64>,
}

impl OtelObserver {
    pub fn new(meter: Meter) -> Self {
        Self {
            wasm_initialization: meter
                .u64_histogram("wasm_initialization")
                .with_unit("microseconds")
                .with_description("Time spent setting up wasm sandbox for invocation")
                .build(),
            wasm_invocation: meter
                .u64_histogram("wasm_invocation")
                .with_unit("microseconds")
                .with_description("Time spent on calling `main` in wasm sandbox")
                .build(),
        }
    }
}
impl Observer for OtelObserver {
    fn wasm_initialization(&self, duration: core::time::Duration) {
        self.wasm_initialization.record(duration.as_micros().try_into().unwrap_or(u64::MAX), &[])
    }

    fn wasm_invocation(&self, duration: core::time::Duration) {
        self.wasm_invocation.record(duration.as_micros().try_into().unwrap_or(u64::MAX), &[])
    }
}

// Equivalent to `tonic::Code::Ok`.
static GRPC_SUCCESS: http::header::HeaderValue = http::header::HeaderValue::from_static("0");

// Equivalent to `tonic::status::GRPC_STATUS_HEADER_CODE`.
const GRPC_STATUS_HEADER_CODE: &str = "grpc-status";

// Tonic limits the incoming RPC size to 4 MB by default; bump it up to 1 GiB.
// We're not sending traffic over a "real" network anyway, after all.
const MAX_DECODING_MESSAGE_SIZE: usize = 1024 * 1024 * 1024;

/// Starts up and serves an OakFunctionsContainersService instance from the
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
    encryption_key_handle: Box<dyn AsyncEncryptionKeyHandle + Send + Sync>,
    observer: OakObserver,
    handler_config: H::HandlerConfig,
) -> anyhow::Result<()>
where
    H: Handler + 'static,
    H::HandlerType: Send + Sync,
{
    tonic::transport::Server::builder()
        .layer(
            tower_http::trace::TraceLayer::new_for_grpc().make_span_with(create_trace).on_response(
                |response: &http::Response<_>, _latency, span: &Span| {
                    // If the request is successful, there's no `grpc-status` header, thus we assume
                    // the request was successful.
                    let code = response
                        .headers()
                        .get(GRPC_STATUS_HEADER_CODE)
                        .unwrap_or(&GRPC_SUCCESS)
                        .to_str()
                        .ok();
                    span.record("rpc.grpc.status_code", code);
                },
            ),
        )
        .layer(tower::load_shed::LoadShedLayer::new())
        .layer(observer.create_monitoring_layer())
        .add_service(
            OakFunctionsServer::new(OakFunctionsContainersService::<H>::new(
                handler_config,
                Arc::from(encryption_key_handle),
                Some(Arc::new(OtelObserver::new(observer.meter))),
            ))
            .max_decoding_message_size(MAX_DECODING_MESSAGE_SIZE)
            .accept_compressed(CompressionEncoding::Gzip),
        )
        .add_service(oak_debug_service::Service::new_server())
        .serve_with_incoming(stream)
        .await
        .context("failed to start up the service")
}
