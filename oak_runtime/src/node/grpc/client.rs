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

//! gRPC client pseudo-Node functionality.

use crate::{
    io::{Receiver, ReceiverExt},
    metrics::Metrics,
    node::{
        grpc::{codec::VecCodec, invocation::Invocation},
        ConfigurationError, Node,
    },
    NodePrivilege, RuntimeProxy,
};
use log::{debug, error, info, trace, warn};
use maplit::hashset;
use oak_abi::{proto::oak::application::GrpcClientConfiguration, Handle, OakStatus};
use oak_io::handle::ReadHandle;
use oak_io::OakError;
use oak_services::proto::{google::rpc, oak::encap::GrpcResponse};
use tokio::sync::oneshot;
use tonic::transport::{Certificate, Channel, ClientTlsConfig, Uri};

/// Struct that represents a gRPC client pseudo-Node.
pub struct GrpcClientNode {
    /// Pseudo-Node name.
    node_name: String,
    /// The URI component of a gRPC server endpoint. Must contain the "Host" element.
    /// https://docs.rs/tonic/0.2.1/tonic/transport/struct.Uri.html
    uri: Uri,
    /// Loaded PEM encoded X.509 TLS root certificate file used to authenticate an external gRPC
    /// service.
    root_tls_certificate: Certificate,
    /// gRPC client to allow re-use of connection across multiple method invocations.
    grpc_client: Option<tonic::client::Grpc<tonic::transport::channel::Channel>>,
    node_privilege: NodePrivilege,
}

/// Checks if URI contains the "Host" element.
fn check_uri(uri: &Uri) -> Result<(), ConfigurationError> {
    uri.authority()
        .filter(|authority| !authority.host().is_empty())
        .map(|_| ())
        .ok_or(ConfigurationError::NoHostElement)
}

fn grpc_client_node_privilege(uri: &Uri) -> NodePrivilege {
    if uri.scheme() == Some(&http::uri::Scheme::HTTPS) {
        // Authority is the host:port portion of the endpoint name.
        if let Some(authority) = uri.authority() {
            NodePrivilege::new(
                hashset! { oak_abi::label::tls_endpoint_tag(&authority.as_str()) },
                hashset! { oak_abi::label::tls_endpoint_tag(&authority.as_str()) },
            )
        } else {
            NodePrivilege::default()
        }
    } else {
        NodePrivilege::default()
    }
}

impl GrpcClientNode {
    /// Creates a new [`GrpcClientNode`] instance, but does not start it.
    pub fn new(
        node_name: &str,
        config: GrpcClientConfiguration,
        root_tls_certificate: Certificate,
    ) -> Result<Self, ConfigurationError> {
        let uri = config.uri.parse().map_err(|error| {
            error!("Error parsing URI {}: {:?}", config.uri, error);
            ConfigurationError::IncorrectURI
        })?;
        check_uri(&uri)?;
        // We compute the node privilege once and for all at start and just store it, since it does
        // not change throughout the node execution.
        let node_privilege = grpc_client_node_privilege(&uri);
        // TODO(#814): Actually check that the newly created node can write to the
        // "public_untrusted" label, taking into account its own label and privilege.
        Ok(Self {
            node_name: node_name.to_string(),
            uri,
            root_tls_certificate,
            grpc_client: None,
            node_privilege,
        })
    }

    /// Main loop that handles gRPC invocations from the `handle`, sends gRPC requests to an
    /// external gRPC service and writes gRPC responses back to the invocation channel.
    async fn handle_loop(
        &mut self,
        runtime: RuntimeProxy,
        handle: Handle,
    ) -> Result<(), OakError> {
        // Create a [`Receiver`] used for reading gRPC invocations.
        let receiver = Receiver::<Invocation>::new(ReadHandle { handle });
        loop {
            debug!("Waiting for gRPC invocation");
            // Read a gRPC invocation from the [`Receiver`].
            let invocation = receiver.receive(&runtime).map_err(|error| {
                match error {
                    OakError::OakStatus(OakStatus::ErrTerminated) => debug!("gRPC client node is terminating."),
                    OakError::OakStatus(OakStatus::ErrChannelClosed) => info!("gRPC invocation channel closed"),
                    _ => error!("Couldn't receive the invocation: {:?}", error),
                }
                error
            })?;

            let result = self.process_invocation(&runtime, &invocation).await;
            info!("Invocation processing finished: {:?}", result);
            if result.is_err() {
                warn!(
                    "Error encountered; forcing re-connection next time around ({:?})",
                    result
                );
                self.grpc_client = None;
            }
            invocation.close(&runtime);
        }
    }

    /// Process a gRPC method invocation for an external gRPC service.
    async fn process_invocation(
        &mut self,
        runtime: &RuntimeProxy,
        invocation: &Invocation,
    ) -> Result<(), OakError> {
        let uri = self.uri.to_string();
        let record_completion_with_error = |method_name, error_code| {
            runtime
                .metrics_data()
                .grpc_client_metrics
                .grpc_client_completed
                .with_label_values(&[&uri, method_name, &format!("{:?}", error_code)])
                .inc();
            // In case of an error, update the latency with zero to keep the counts consistent.
            runtime
                .metrics_data()
                .grpc_client_metrics
                .grpc_client_completed_latency_seconds
                .with_label_values(&[&uri, method_name])
                .observe(0_f64);
        };
        let send_error = |code, msg| {
            invocation.send_error(code, msg, runtime);
            // Update the number of started requests to keep the counts consistent.
            runtime
                .metrics_data()
                .grpc_client_metrics
                .observe_new_request(&uri, "unknown", 0);
            record_completion_with_error("unknown", code);
        };

        // Receive a request from the invocation channel.
        let request = invocation.receive_request(&runtime).map_err(|error| {
            send_error(rpc::Code::Internal, "Failed to read request");
            error!(
                "Couldn't read gRPC request from the invocation: {:?}",
                error
            );
            error
        })?;
        debug!("Incoming gRPC request: {:?}", request);

        if self.grpc_client.is_none() {
            // Connect to an external gRPC service.
            self.grpc_client = Some(self.connect().await.map_err(|error| {
                error!("Couldn't connect to {}: {:?}", self.uri, error);
                send_error(rpc::Code::NotFound, "Service connection failed");
                OakStatus::ErrInternal
            })?);
        }
        let grpc_client = self.grpc_client.as_mut().unwrap();
        grpc_client.ready().await.map_err(|error| {
            error!("Service was not ready: {}", error);
            send_error(rpc::Code::NotFound, "Service not ready");
            OakStatus::ErrInternal
        })?;

        let codec = VecCodec::default();
        let path = request.method_name.parse().map_err(|error| {
            error!("Invalid URI {}: {}", request.method_name, error);
            send_error(rpc::Code::InvalidArgument, "Invalid URI");
            OakStatus::ErrInternal
        })?;

        let method_name = request.method_name;
        runtime
            .metrics_data()
            .grpc_client_metrics
            .observe_new_request(&uri, &method_name, request.req_msg.len());

        // Forward the request to the external gRPC service and wait for the response(s).
        let request = tonic::Request::new(request.req_msg);
        let request_stream =
            request.map(|m| futures_util::stream::once(futures_util::future::ready(m)));
        let rsp_stream = match grpc_client.streaming(request_stream, path, codec).await {
            Ok(rsp_stream) => rsp_stream,
            Err(error) => {
                error!("Request to remote service failed: {}", error);
                let error_code = tonic_code_to_grpc(error.code());
                invocation.send_error(error_code, error.message(), runtime);
                record_completion_with_error(&method_name, error_code);
                return Ok(());
            }
        };

        let mut response_handler =
            ResponseHandler::new(runtime.clone(), rsp_stream, invocation, uri, method_name);
        response_handler.handle().await
    }

    /// Creates a TLS connection to an external gRPC service.
    async fn connect(
        &self,
    ) -> Result<tonic::client::Grpc<tonic::transport::channel::Channel>, tonic::transport::Error>
    {
        debug!("Connecting to {}", self.uri);

        // Create a TLS configuration.
        let tls_config = ClientTlsConfig::new().ca_certificate(self.root_tls_certificate.clone());

        // Connect to a remote gRPC service.
        let connection = Channel::builder(self.uri.clone())
            .tls_config(tls_config)
            .expect("Couldn't create TLS configuration")
            .connect()
            .await?;

        debug!("Connected to {}", self.uri);
        Ok(tonic::client::Grpc::new(connection))
    }
}

struct MetricsRecorder {
    metrics_data: Metrics,
    server: String,
    method_name: String,
    msg_count: u32,
    status_code: rpc::Code,
    _timer: prometheus::HistogramTimer,
}

impl MetricsRecorder {
    fn new(runtime: RuntimeProxy, server: String, method_name: String) -> MetricsRecorder {
        let metrics_data = runtime.metrics_data();
        let timer = metrics_data
            .grpc_client_metrics
            .start_timer(&server, &method_name);
        MetricsRecorder {
            metrics_data,
            server,
            method_name,
            msg_count: 0,
            status_code: rpc::Code::Ok,
            _timer: timer,
        }
    }

    fn update_status_code(&mut self, status_code: rpc::Code) {
        self.status_code = status_code;
    }

    fn observe_message_with_len(&mut self, msg_len: usize) {
        self.msg_count += 1;
        self.metrics_data
            .grpc_client_metrics
            .observe_new_response_message(&self.server, &self.method_name, msg_len);
    }

    fn observe_completion(&self) {
        self.metrics_data
            .grpc_client_metrics
            .observe_response_handling_completed(
                &self.server,
                &self.method_name,
                &format!("{:?}", self.status_code),
                self.msg_count,
            );
    }
}

impl Drop for MetricsRecorder {
    fn drop(&mut self) {
        trace!(
            "Dropping MetricsRecorder for '{}:{}'.",
            self.server,
            self.method_name,
        );
        self.observe_completion();
        // Note that dropping self._timer will record the duration.
    }
}

struct ResponseHandler<'a> {
    runtime: RuntimeProxy,
    response_stream: tonic::Response<tonic::Streaming<Vec<u8>>>,
    invocation: &'a Invocation,
    // The lifetime of the metrics recorder matches the lifetime of the
    // response handler, updating the metrics when the handler is dropped.
    metrics_recorder: MetricsRecorder,
}

impl<'a> ResponseHandler<'a> {
    fn new(
        runtime: RuntimeProxy,
        response_stream: tonic::Response<tonic::Streaming<Vec<u8>>>,
        invocation: &'a Invocation,
        server: String,
        method_name: String,
    ) -> Self {
        let metrics_recorder = MetricsRecorder::new(runtime.clone(), server, method_name);
        ResponseHandler {
            runtime,
            response_stream,
            invocation,
            metrics_recorder,
        }
    }

    async fn handle(&mut self) -> Result<(), OakError> {
        let body_stream = self.response_stream.get_mut();
        loop {
            let metrics_recorder = &mut self.metrics_recorder;
            let invocation = self.invocation;
            let runtime = &self.runtime.clone();
            let message = body_stream.message().await.map_err(|error| {
                error!("Failed to read response: {}", error);
                invocation.send_error(rpc::Code::Internal, "Failed to read response", runtime);
                metrics_recorder.update_status_code(rpc::Code::Internal);
                OakStatus::ErrInternal
            })?;

            if let Some(message) = message {
                let msg_len = message.len();
                let encap_rsp = GrpcResponse {
                    rsp_msg: message,
                    status: None,
                    last: false,
                };
                // Send the response back to the invocation channel.
                debug!("Sending gRPC response: {:?}", encap_rsp);
                invocation
                    .send_response(encap_rsp, runtime)
                    .map_err(|error| {
                        error!("Couldn't send gRPC response to the invocation: {:?}", error);
                        error
                    })?;
                metrics_recorder.observe_message_with_len(msg_len);
            } else {
                debug!("No message available, close out method invocation");
                break;
            }
        }

        Ok(())
    }
}

/// Oak Node implementation for the gRPC client pseudo-Node.
impl Node for GrpcClientNode {
    fn run(
        mut self: Box<Self>,
        runtime: RuntimeProxy,
        handle: Handle,
        notify_receiver: oneshot::Receiver<()>,
    ) {
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
            .expect("Couldn't create an Async runtime");

        // Listen to incoming gRPC invocations.
        info!(
            "{}: Starting gRPC client pseudo-Node thread",
            self.node_name
        );
        async_runtime.block_on(futures::future::select(
            Box::pin(self.handle_loop(runtime, handle)),
            notify_receiver,
        ));
        info!("{}: Exiting gRPC client pseudo-Node thread", self.node_name);
    }

    fn get_privilege(&self) -> NodePrivilege {
        self.node_privilege.clone()
    }
}

fn tonic_code_to_grpc(code: tonic::Code) -> rpc::Code {
    match code {
        tonic::Code::Ok => rpc::Code::Ok,
        tonic::Code::Cancelled => rpc::Code::Cancelled,
        tonic::Code::Unknown => rpc::Code::Unknown,
        tonic::Code::InvalidArgument => rpc::Code::InvalidArgument,
        tonic::Code::DeadlineExceeded => rpc::Code::DeadlineExceeded,
        tonic::Code::NotFound => rpc::Code::NotFound,
        tonic::Code::AlreadyExists => rpc::Code::AlreadyExists,
        tonic::Code::PermissionDenied => rpc::Code::PermissionDenied,
        tonic::Code::ResourceExhausted => rpc::Code::ResourceExhausted,
        tonic::Code::FailedPrecondition => rpc::Code::FailedPrecondition,
        tonic::Code::Aborted => rpc::Code::Aborted,
        tonic::Code::OutOfRange => rpc::Code::OutOfRange,
        tonic::Code::Unimplemented => rpc::Code::Unimplemented,
        tonic::Code::Internal => rpc::Code::Internal,
        tonic::Code::Unavailable => rpc::Code::Unavailable,
        tonic::Code::DataLoss => rpc::Code::DataLoss,
        tonic::Code::Unauthenticated => rpc::Code::Unauthenticated,
        _ => rpc::Code::Unknown,
    }
}
