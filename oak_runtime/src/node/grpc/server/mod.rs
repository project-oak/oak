//
// Copyright 2020 The Project Oak Authors
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

//! gRPC server pseudo-Node functionality.

use crate::{
    auth::oidc_utils::ClientInfo,
    io::{ReceiverExt, SenderExt},
    metrics::Metrics,
    node::{
        grpc::{codec::VecCodec, to_tonic_status},
        ConfigurationError, Node,
    },
    proto::oak::invocation::{GrpcInvocation, GrpcInvocationSender},
    RuntimeProxy,
};
use hyper::service::Service;
use log::{debug, error, info, trace, warn};
use oak_abi::{label::Label, proto::oak::application::GrpcServerConfiguration, OakStatus};
use oak_io::{
    handle::{ReadHandle, WriteHandle},
    OakError, Receiver, Sender,
};
use oak_services::proto::{
    google::rpc,
    oak::encap::{GrpcRequest, GrpcResponse},
};
use prost::Message;
use std::{
    net::SocketAddr,
    task::{Context, Poll},
};
use tokio::sync::{mpsc, oneshot};
use tonic::{
    codegen::BoxFuture,
    metadata::MetadataMap,
    server::{Grpc, ServerStreamingService},
    transport::{Identity, NamedService},
};

mod auth;

/// Struct that represents a gRPC server pseudo-Node.
pub struct GrpcServerNode {
    /// Pseudo-Node name.
    node_name: String,
    /// Server address to listen client requests on.
    address: SocketAddr,
    /// Loaded files containing a server TLS key and certificates.
    tls_identity: Identity,
    /// OpenID Connect Authentication client information. A value of `None` will mean that the
    /// server will not support OpenID Connect authentication.
    oidc_client_info: Option<ClientInfo>,
}

/// Checks if port is greater than 1023.
fn check_port(address: &SocketAddr) -> Result<(), ConfigurationError> {
    if address.port() > 1023 {
        Ok(())
    } else {
        Err(ConfigurationError::IncorrectPort)
    }
}

impl GrpcServerNode {
    /// Creates a new [`GrpcServerNode`] instance, but does not start it.
    pub fn new(
        node_name: &str,
        config: GrpcServerConfiguration,
        tls_identity: Identity,
        oidc_client_info: Option<ClientInfo>,
    ) -> Result<Self, ConfigurationError> {
        let address = config.address.parse()?;
        check_port(&address)?;
        Ok(Self {
            node_name: node_name.to_string(),
            address,
            tls_identity,
            oidc_client_info,
        })
    }

    /// Reads the [`WriteHandle`] (to be used for sending new invocations) from a startup channel.
    /// Returns an error if the startup channel couldn't be read, or if the initial message is
    /// invalid (it must be an encoded [`GrpcInvocationSender`]).
    fn get_invocation_channel(
        runtime: &RuntimeProxy,
        startup_handle: oak_abi::Handle,
    ) -> Result<WriteHandle, OakError> {
        let startup_receiver = Receiver::<GrpcInvocationSender>::new(ReadHandle {
            handle: startup_handle,
        });
        let invocation_channel = startup_receiver.receive(&runtime)?;
        match &invocation_channel.sender {
            Some(invocation_sender) => {
                info!(
                    "Invocation channel write handle received: {}",
                    invocation_sender.handle.handle
                );
                Ok(invocation_sender.handle)
            }
            None => {
                error!("Couldn't receive the invocation sender.");
                Err(OakError::OakStatus(OakStatus::ErrBadHandle))
            }
        }
    }
}

/// Oak Node implementation for the gRPC server.
impl Node for GrpcServerNode {
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        startup_handle: oak_abi::Handle,
        notify_receiver: oneshot::Receiver<()>,
    ) {
        // At start-of-day we need/expect to receive a write handle for an invocation channel
        // to use for all subsequent activity.
        info!("{}: Waiting for invocation channel", self.node_name);
        let invocation_channel =
            match GrpcServerNode::get_invocation_channel(&runtime, startup_handle) {
                Ok(writer) => writer,
                Err(status) => {
                    error!(
                        "Failed to retrieve invocation channel write handle: {:?}",
                        status
                    );
                    return;
                }
            };
        if let Err(err) = runtime.channel_close(startup_handle) {
            error!(
                "Failed to close initial inbound channel {}: {:?}",
                startup_handle, err
            );
        }

        // Build a service to process incoming authentication gRPC requests.
        let auth_handler = match self.oidc_client_info {
            Some(auth_config) => auth::oidc_service::build_service(
                &auth_config.client_id,
                &auth_config.client_secret,
            ),
            // TODO(#1021): Add better handling to cases where the client info is not supplied.
            _ => auth::oidc_service::build_service("", ""),
        };

        // Build a service to process all other incoming HTTP/2 requests.
        let generic_handler = HttpRequestHandler {
            runtime,
            invocation_channel,
        };

        let server = tonic::transport::Server::builder()
            .tls_config(tonic::transport::ServerTlsConfig::new().identity(self.tls_identity))
            .expect("Couldn't create TLS configuration")
            // The order for adding services are important. The namespaces of the services are
            // checked in the reverse order to which it was added. The `generic_handler` should
            // be added first so that it is checked last, otherwise it would handle requests
            // intended for other services.
            .add_service(generic_handler)
            .add_service(auth_handler)
            .serve_with_shutdown(self.address, async {
                // Treat notification failure the same as a notification.
                let _ = notify_receiver.await;
            });

        // Create an Async runtime for executing futures.
        // https://docs.rs/tokio/
        let mut async_runtime = tokio::runtime::Builder::new()
            // Use simple scheduler that runs all tasks on the current-thread.
            // https://docs.rs/tokio/0.2.16/tokio/runtime/index.html#basic-scheduler
            .basic_scheduler()
            // Enables the I/O driver.
            // Necessary for using net, process, signal, and I/O types on the Tokio runtime.
            .enable_io()
            // Enables the time driver.
            // Necessary for creating a Tokio Runtime.
            .enable_time()
            .build()
            .expect("Couldn't create Async runtime");

        // Start the gRPC server.
        info!(
            "{}: Starting gRPC server pseudo-Node on: {}",
            self.node_name, self.address
        );
        match async_runtime.block_on(server) {
            Err(err) => warn!(
                "{}: Error running gRPC server pseudo-Node: {}",
                self.node_name, err
            ),
            Ok(()) => {
                info!(
                    "{}: Success running gRPC server pseudo-Node",
                    self.node_name,
                );
            }
        }
    }
}

/// [`HttpRequestHandler`] handles HTTP/2 requests from a client and sends HTTP/2 responses back.
#[derive(Clone)]
struct HttpRequestHandler {
    /// Reference to the Runtime in the context of this gRPC server pseudo-Node.
    runtime: RuntimeProxy,
    /// Channel handle used for writing gRPC invocations.
    invocation_channel: WriteHandle,
}

/// Set a mandatory prefix for all gRPC requests processed by a gRPC pseudo-Node.
impl NamedService for HttpRequestHandler {
    const NAME: &'static str = "";
}

impl Service<http::Request<hyper::Body>> for HttpRequestHandler {
    type Response = http::Response<tonic::body::BoxBody>;
    type Error = http::Error;
    type Future = BoxFuture<Self::Response, Self::Error>;

    fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    /// Decodes a gRPC request using a [`VecCodec`] and processes it with
    /// [`tonic::server::Grpc::server_streaming`] and an ephemeral [`GrpcInvocationHandler`].
    fn call(&mut self, request: http::Request<hyper::Body>) -> Self::Future {
        let grpc_handler = GrpcInvocationHandler::new(
            self.runtime.clone(),
            Sender::<GrpcInvocation>::new(self.invocation_channel),
            request.uri().path().to_string(),
        );

        let method_name = request.uri().path().to_string();
        let metrics_data = self.runtime.metrics_data();
        let future = async move {
            debug!("Processing HTTP/2 request: {:?}", request);
            let mut grpc_service = Grpc::new(VecCodec::default());
            let response = grpc_service.server_streaming(grpc_handler, request).await;
            debug!("Sending HTTP/2 response: {:?}", response);
            let stc = format!("{}", response.status());
            metrics_data
                .grpc_server_metrics
                .grpc_server_handled_total
                .with_label_values(&[&method_name, &stc])
                .inc();
            Ok(response)
        };

        Box::pin(future)
    }
}

impl From<OakLabelError> for tonic::Status {
    fn from(v: OakLabelError) -> Self {
        match v {
            OakLabelError::MissingLabel => tonic::Status::invalid_argument("Missing Oak Label"),
            OakLabelError::MultipleLabels => tonic::Status::invalid_argument("Multiple Oak Labels"),
            OakLabelError::InvalidLabel => tonic::Status::invalid_argument("Invalid Oak Label"),
        }
    }
}

enum OakLabelError {
    MissingLabel,
    MultipleLabels,
    InvalidLabel,
}

/// Returns the [`Label`] defined as part of the the metadata of an incoming gRPC request.
///
/// Returns an error if there is not exactly one label specified by the caller:
///
/// - no labels means that the caller did not specify any IFC restrictions, which is probably a
///   mistake
/// - more than one labels means that the caller specified multiple IFC restrictions; if the
///   intention was to allow multiple alternative ones, they need to be combined in a single label,
///   once conjunctions are supported
fn get_oak_label(metadata_map: &MetadataMap) -> Result<Label, OakLabelError> {
    let labels = metadata_map
        .get_all_bin(oak_abi::OAK_LABEL_GRPC_METADATA_KEY)
        .iter()
        .collect::<Vec<_>>();
    if labels.is_empty() {
        warn!(
            "incorrect number of gRPC labels found: {}, expected: 1",
            labels.len()
        );
        return Err(OakLabelError::MissingLabel);
    }
    if labels.len() >= 2 {
        warn!(
            "incorrect number of gRPC labels found: {}, expected: 1",
            labels.len()
        );
        return Err(OakLabelError::MultipleLabels);
    }
    let label_bytes = labels[0].to_bytes().map_err(|err| {
        warn!("could not convert gRPC label to bytes: {}", err);
        OakLabelError::InvalidLabel
    })?;
    oak_abi::proto::oak::label::Label::decode(label_bytes).map_err(|err| {
        warn!("could not parse gRPC label: {}", err);
        OakLabelError::InvalidLabel
    })
}

/// Handler for an individual gRPC method invocation.
#[derive(Clone)]
struct GrpcInvocationHandler {
    /// Reference to the Runtime in the context of this gRPC server pseudo-Node.
    runtime: RuntimeProxy,
    /// Channel handle used for writing gRPC invocations.
    invocation_channel: Sender<GrpcInvocation>,
    /// Name of the gRPC method being invoked.
    method_name: String,
}

type SerializedResponseStream = mpsc::UnboundedReceiver<Result<Vec<u8>, tonic::Status>>;

impl ServerStreamingService<Vec<u8>> for GrpcInvocationHandler {
    type Response = Vec<u8>;
    type ResponseStream = SerializedResponseStream;
    type Future = BoxFuture<tonic::Response<SerializedResponseStream>, tonic::Status>;

    fn call(&mut self, request: tonic::Request<Vec<u8>>) -> Self::Future {
        let handler = self.clone();
        let metrics_data = self.runtime.metrics_data();
        // Build a future of type `Future<Output = Result<SerializedResponseStream, tonic::Status>>`
        let future = async move {
            metrics_data
                .grpc_server_metrics
                .grpc_server_started_total
                .with_label_values(&[&handler.method_name])
                .inc();
            let oak_label = get_oak_label(request.metadata())?;
            info!(
                "handling gRPC request; peer address: {}, method: {}, request size: {} bytes, label: {:?}",
                // TODO(#1089): Ensure that the client address is available.
                request.remote_addr().map(|addr| addr.to_string()).unwrap_or_else(|| "<unknown>".to_string()),
                handler.method_name,
                request.get_ref().len(),
                oak_label
            );
            // Create an encapsulated gRPC request.
            // TODO(#97): Add client-streaming support.
            let grpc_request = GrpcRequest {
                method_name: handler.method_name.to_string(),
                req_msg: request.into_inner(),
                last: true,
            };

            // Inject the encapsulated gRPC request into the Oak Application.
            debug!("inject encapsulated request into Oak Node");
            let response_iter = handler
                .inject_grpc_request(grpc_request, &oak_label)
                .map_err(|()| tonic::Status::new(tonic::Code::Internal, ""))?;
            let (tx, rx) = mpsc::unbounded_channel();

            // Spawn a separate thread to handle responses, because the underlying call to
            // Runtime::wait_on_channels() blocks.
            // TODO(#1376): make wait_on_channels() better integrated with `async` so we don't
            // have to mix threads and async.
            std::thread::spawn(move || {
                for response in response_iter {
                    debug!("Returning gRPC response: {:?}", response);
                    let result = match response.status {
                        None => Ok(response.rsp_msg),
                        Some(status) if status.code == rpc::Code::Ok as i32 => Ok(response.rsp_msg),
                        Some(status) => Err(to_tonic_status(status)),
                    };
                    tx.send(result).unwrap();
                }
            });
            Ok(tonic::Response::new(rx))
        };

        Box::pin(future)
    }
}

impl GrpcInvocationHandler {
    fn new(
        runtime: RuntimeProxy,
        invocation_channel: Sender<GrpcInvocation>,
        method_name: String,
    ) -> Self {
        Self {
            runtime,
            invocation_channel,
            method_name,
        }
    }

    /// Send an encapsulated gRPC request into the Oak Application as an invocation.
    /// Returns an [`oak_abi::Handle`] for reading gRPC response(s) from.
    fn inject_grpc_request(
        &self,
        request: GrpcRequest,
        label: &Label,
    ) -> Result<GrpcResponseIterator, ()> {
        // Create a pair of temporary channels to pass the gRPC request and to receive the response.

        // The channel containing the request is created with the label specified by the caller.
        // This will fail if the label has a non-empty integrity component.
        let (request_writer, request_reader) =
            self.runtime.channel_create(&label).map_err(|err| {
                warn!("could not create gRPC request channel: {:?}", err);
            })?;
        let (response_writer, response_reader) = self
            .runtime
            .channel_create(&Label::public_untrusted())
            .map_err(|err| {
                warn!("could not create gRPC response channel: {:?}", err);
            })?;

        let invocation = GrpcInvocation {
            receiver: Some(Receiver::<GrpcRequest>::new(ReadHandle {
                handle: request_reader,
            })),
            sender: Some(Sender::<GrpcResponse>::new(WriteHandle {
                handle: response_writer,
            })),
        };

        // Put the gRPC request message inside the per-invocation request channel.
        Sender::<GrpcRequest>::new(WriteHandle {
            handle: request_writer,
        })
        .send(request, &self.runtime)
        .map_err(|error| {
            error!(
                "Couldn't write message to the gRPC request channel: {:?}",
                error
            );
        })?;

        // Send an invocation message (with attached handles) to the Oak Node.
        self.invocation_channel
            .send(invocation, &self.runtime)
            .map_err(|error| {
                error!("Couldn't write gRPC invocation message: {:?}", error);
            })?;

        // Close all local handles except for the one that allows reading responses.
        if let Err(err) = self.runtime.channel_close(request_writer) {
            error!(
                "Failed to close request writer channel for invocation: {:?}",
                err
            );
        }
        if let Err(err) = self.runtime.channel_close(request_reader) {
            error!(
                "Failed to close request reader channel for invocation: {:?}",
                err
            );
        }
        if let Err(err) = self.runtime.channel_close(response_writer) {
            error!(
                "Failed to close response writer channel for invocation: {:?}",
                err
            );
        }

        Ok(GrpcResponseIterator::new(
            self.runtime.clone(),
            ReadHandle {
                handle: response_reader,
            },
            self.method_name.clone(),
        ))
    }
}

struct MetricsRecorder {
    metrics_data: Metrics,
    method_name: String,
    msg_count: u32,
    _timer: prometheus::HistogramTimer,
}

impl MetricsRecorder {
    fn new(runtime: RuntimeProxy, method_name: String) -> MetricsRecorder {
        let metrics_data = runtime.metrics_data();
        let timer = metrics_data
            .grpc_server_metrics
            .grpc_server_handled_latency_seconds
            .with_label_values(&[&method_name])
            .start_timer();
        MetricsRecorder {
            metrics_data,
            method_name,
            msg_count: 0,
            _timer: timer,
        }
    }

    fn observe_message_with_len(&mut self, msg_len: usize) {
        self.msg_count += 1;
        self.metrics_data
            .grpc_server_metrics
            .grpc_server_response_size_bytes
            .with_label_values(&[&self.method_name])
            .observe(msg_len as f64);
    }

    fn observe_completion(&self) {
        self.metrics_data
            .grpc_server_metrics
            .grpc_server_msg_sent_total
            .with_label_values(&[&self.method_name])
            .observe(self.msg_count as f64);
    }
}

impl Drop for MetricsRecorder {
    fn drop(&mut self) {
        self.observe_completion();
    }
    // Note that dropping self._timer will record the duration.
}

struct GrpcResponseIterator {
    runtime: RuntimeProxy,
    response_reader: Option<Receiver<GrpcResponse>>,
    method_name: String,
    // The lifetime of the metrics_recorder matches the lifetime of the
    // iterator, updating the metrics when the iterator is dropped.
    metrics_recorder: MetricsRecorder,
    done: bool,
}

impl GrpcResponseIterator {
    fn new(runtime: RuntimeProxy, response_read_handle: ReadHandle, method_name: String) -> Self {
        trace!(
            "Create new GrpcResponseIterator for '{}', reading from {}",
            method_name,
            response_read_handle.handle
        );
        let metrics_recorder = MetricsRecorder::new(runtime.clone(), method_name.clone());
        let response_reader = Some(Receiver::<GrpcResponse>::new(response_read_handle));
        GrpcResponseIterator {
            runtime,
            response_reader,
            method_name,
            metrics_recorder,
            done: false,
        }
    }
}

/// Manual implementation of the `Drop` trait to ensure the response channel
/// is always closed.
impl Drop for GrpcResponseIterator {
    fn drop(&mut self) {
        if let Some(receiver) = self.response_reader.take() {
            trace!(
                "Dropping GrpcResponseIterator for '{}': close channel {}",
                self.method_name,
                receiver.handle.handle
            );
            if let Err(err) = receiver.close(&self.runtime) {
                error!("Failed to close gRPC response reader channel: {:?}", err);
            }
        }
        // Note that dropping self.metrics_recorder will record the duration, and update the
        // `grpc_server_msg_sent_total` metric.
    }
}

impl Iterator for GrpcResponseIterator {
    type Item = GrpcResponse;

    /// Read a single encapsulated gRPC response from the provided channel.
    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        match &self.response_reader {
            Some(receiver) => {
                match receiver.receive(&self.runtime) {
                    Ok(grpc_rsp) => {
                        self.metrics_recorder
                            .observe_message_with_len(grpc_rsp.rsp_msg.len());
                        if grpc_rsp.last {
                            // The Node has definitively marked this as the last response for this
                            // invocation; keep track of this and don't bother attempting to read
                            // from the response channel next time around.
                            //
                            // Note that the reverse isn't always true: the final response for a
                            // server-streaming method might *not* have last=true; in that case the
                            // next attempt to read from the response channel will find a closed
                            // channel, and so we treat that as the end of the method invocation
                            // (below).
                            self.done = true;
                        }
                        trace!(
                            "Return response of size {}, status={:?} last={}",
                            grpc_rsp.rsp_msg.len(),
                            grpc_rsp.status,
                            grpc_rsp.last
                        );
                        Some(grpc_rsp)
                    }
                    Err(error) => {
                        error!("Error reading gRPC response: {:?}", error);
                        None
                    }
                }
            }
            None => None,
        }
    }
}
