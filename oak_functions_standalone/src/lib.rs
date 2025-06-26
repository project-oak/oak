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
    pin::Pin,
    sync::{Arc, OnceLock},
};

use anyhow::Context;
use oak_containers_agent::metrics::OakObserver;
use oak_functions_service::{instance::OakFunctionsInstance, Handler, Observer};
use oak_grpc::oak::functions::standalone::oak_functions_session_server::{
    OakFunctionsSession, OakFunctionsSessionServer,
};
use oak_proto_rust::oak::functions::{
    standalone::{OakSessionRequest, OakSessionResponse},
    ExtendNextLookupDataRequest, ExtendNextLookupDataResponse, FinishNextLookupDataRequest,
    FinishNextLookupDataResponse, InitializeRequest, InitializeResponse, ReserveRequest,
    ReserveResponse,
};
use opentelemetry::metrics::{Histogram, Meter};
use tokio::io::{AsyncRead, AsyncWrite};
use tokio_stream::Stream;
use tonic::{codec::CompressionEncoding, transport::server::Connected};
use tracing::Span;

// Arguements to start up the Oak Functions Session Service.
// While currently there is only one argument, in the future lookup data
// arguments will be added.
pub struct OakFunctionsSessionArgs {
    pub wasm_initialization: InitializeRequest,
}

// Instance of the OakFunctions service for Oak Containers.
pub struct OakFunctionsSessionService<H: Handler> {
    instance_config: H::HandlerConfig,
    instance: OnceLock<OakFunctionsInstance<H>>,
    observer: Option<Arc<dyn Observer + Send + Sync>>,
}

impl<H: Handler> OakFunctionsSessionService<H> {
    pub fn startup(
        instance_config: H::HandlerConfig,
        observer: Option<Arc<dyn Observer + Send + Sync>>,
        oak_functions_session_args: OakFunctionsSessionArgs,
    ) -> Self {
        let oak_functions_session_service =
            OakFunctionsSessionService { instance_config, instance: OnceLock::new(), observer };
        // Initialize the OakFuncitonsInstance.
        if let Err(e) =
            oak_functions_session_service.initialize(oak_functions_session_args.wasm_initialization)
        {
            eprintln!("Error initializing OakFunctionsSessionService: {:?}", e);
            panic!("Initialization failed!"); // Or propagate the error
        }

        // TODO: b/424407998 - Load lookup data via calls to `reserve`,
        // `finish_next_lookup_data`, and `extend_next_lookup_data`.
        oak_functions_session_service
    }

    fn initialize(&self, request: InitializeRequest) -> tonic::Result<InitializeResponse> {
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
                Ok(InitializeResponse::default())
            }
        }
    }

    pub fn extend_next_lookup_data(
        &self,
        request: ExtendNextLookupDataRequest,
    ) -> tonic::Result<ExtendNextLookupDataResponse> {
        self.get_instance()?.extend_next_lookup_data(request).map_err(map_status)
    }

    pub fn finish_next_lookup_data(
        &self,
        request: FinishNextLookupDataRequest,
    ) -> tonic::Result<FinishNextLookupDataResponse> {
        self.get_instance()?.finish_next_lookup_data(request).map_err(map_status)
    }

    pub fn reserve(&self, request: ReserveRequest) -> tonic::Result<ReserveResponse> {
        self.get_instance()?.reserve(request).map_err(map_status)
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

type ServerStreaming =
    Pin<Box<dyn Stream<Item = Result<OakSessionResponse, tonic::Status>> + Send>>;

#[tonic::async_trait]
impl<H> OakFunctionsSession for OakFunctionsSessionService<H>
where
    H: Handler + 'static,
    H::HandlerType: Send + Sync,
{
    type OakSessionStream = ServerStreaming;

    async fn oak_session(
        &self,
        _request: tonic::Request<tonic::Streaming<OakSessionRequest>>,
    ) -> Result<tonic::Response<Self::OakSessionStream>, tonic::Status> {
        Err(tonic::Status::unimplemented("OakSession is not implemented"))
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
                .init(),
            wasm_invocation: meter
                .u64_histogram("wasm_invocation")
                .with_unit("microseconds")
                .with_description("Time spent on calling `main` in wasm sandbox")
                .init(),
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
    observer: OakObserver,
    handler_config: H::HandlerConfig,
    oak_functions_session_args: OakFunctionsSessionArgs,
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
            OakFunctionsSessionServer::new(OakFunctionsSessionService::<H>::startup(
                handler_config,
                Some(Arc::new(OtelObserver::new(observer.meter))),
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
