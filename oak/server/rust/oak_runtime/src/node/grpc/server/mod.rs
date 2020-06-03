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
    node::{
        grpc::{codec::VecCodec, to_tonic_status},
        ConfigurationError, Node,
    },
    runtime::RuntimeProxy,
};
use hyper::service::Service;
use log::{debug, error, info, warn};
use oak_abi::{
    label::Label,
    proto::oak::{
        application::GrpcServerConfiguration,
        encap::{GrpcRequest, GrpcResponse},
    },
    ChannelReadStatus, OakStatus,
};
use prost::Message;
use std::{
    net::SocketAddr,
    task::{Context, Poll},
};
use tokio::sync::oneshot;
use tonic::{
    codegen::BoxFuture,
    metadata::MetadataMap,
    server::{Grpc, UnaryService},
    transport::{Identity, NamedService},
};

mod auth;

// The `-bin` suffix allows sending binary data for this metadata key.
//
// See https://github.com/grpc/grpc/blob/master/doc/PROTOCOL-HTTP2.md.
//
// Keep in sync with /oak/common/label.cc.
const OAK_LABEL_GRPC_METADATA_KEY: &str = "x-oak-label-bin";

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

    /// Reads an [`oak_abi::Handle`] from a channel specified by `handle`.
    /// Returns an error if couldn't read from the channel or if received a wrong number of handles
    /// (not equal to 1).
    fn get_channel_writer(
        runtime: &RuntimeProxy,
        handle: oak_abi::Handle,
    ) -> Result<oak_abi::Handle, OakStatus> {
        let read_status = runtime.wait_on_channels(&[handle]).map_err(|error| {
            error!("Couldn't wait on the initial reader handle: {:?}", error);
            OakStatus::ErrInternal
        })?;

        let channel_writer = if read_status[0] == ChannelReadStatus::ReadReady {
            runtime
                .channel_read(handle)
                .map_err(|error| {
                    error!("Couldn't read from the initial reader handle {:?}", error);
                    OakStatus::ErrInternal
                })
                .and_then(|message| {
                    message
                        .ok_or_else(|| {
                            error!("Empty message");
                            OakStatus::ErrInternal
                        })
                        .and_then(|m| {
                            if m.handles.len() == 1 {
                                Ok(m.handles[0])
                            } else {
                                error!(
                                    "gRPC server pseudo-node should receive a single writer handle, found {}",
                                    m.handles.len()
                                );
                                Err(OakStatus::ErrInternal)
                            }
                        })
                })
        } else {
            error!("Couldn't read channel: {:?}", read_status[0]);
            Err(OakStatus::ErrInternal)
        }?;

        info!("Channel writer received: {:?}", channel_writer);
        Ok(channel_writer)
    }
}

/// Oak Node implementation for the gRPC server.
impl Node for GrpcServerNode {
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        notify_receiver: oneshot::Receiver<()>,
    ) {
        // Receive a `channel_writer` handle used to pass handles for temporary channels.
        info!("{}: Waiting for a channel writer", self.node_name);
        let channel_writer = GrpcServerNode::get_channel_writer(&runtime, handle)
            .expect("Couldn't initialize a channel writer");

        // Handles incoming authentication gRPC requests
        let auth_handler = match self.oidc_client_info {
            Some(auth_config) => auth::oidc_service::build_service(
                &auth_config.client_id,
                &auth_config.client_secret,
            ),
            // TODO(#1021): Add better handling to cases where the client info is not supplied.
            _ => auth::oidc_service::build_service("", ""),
        };

        // Handles incoming TLS connections, unpacks HTTP/2 requests and forwards them to
        // [`HttpRequestHandler::handle`].
        let generic_handler = HttpRequestHandler {
            runtime,
            writer: channel_writer,
        };

        let server = tonic::transport::Server::builder()
            .tls_config(tonic::transport::ServerTlsConfig::new().identity(self.tls_identity))
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
            .expect("Couldn't create an Async runtime");

        // Start a gRPC server.
        info!(
            "{}: Starting a gRPC server pseudo-Node on: {}",
            self.node_name, self.address
        );
        let result = async_runtime.block_on(server);
        info!(
            "{}: Exiting gRPC server pseudo-Node thread: {:?}",
            self.node_name, result
        );
    }
}

/// [`HttpRequestHandler`] handles HTTP/2 requests from a client and sends HTTP/2 responses back.
#[derive(Clone)]
struct HttpRequestHandler {
    /// Reference to a Runtime that corresponds to a node that created a gRPC server pseudo-Node.
    runtime: RuntimeProxy,
    /// Channel handle used for writing gRPC invocations.
    writer: oak_abi::Handle,
}

/// Set a mandatory prefix for all gRPC requests processed by a gRPC pseudo-Node.
impl NamedService for HttpRequestHandler {
    const NAME: &'static str = "oak";
}

impl Service<http::Request<hyper::Body>> for HttpRequestHandler {
    type Response = http::Response<tonic::body::BoxBody>;
    type Error = http::Error;
    type Future = BoxFuture<Self::Response, Self::Error>;

    fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    /// Decodes an unary gRPC request using a [`VecCodec`] and processes it with
    /// [`tonic::server::Grpc::unary`] and a [`GrpcRequestHandler`].
    fn call(&mut self, request: http::Request<hyper::Body>) -> Self::Future {
        let grpc_handler = GrpcRequestHandler::new(
            self.runtime.clone(),
            self.writer,
            request.uri().path().to_string(),
            MetadataMap::from_headers(request.headers().clone()),
        );

        let method_name = request.uri().path().to_string();
        let metrics_data = self.runtime.metrics_data();
        let future = async move {
            debug!("Processing HTTP/2 request: {:?}", request);
            let mut grpc_service = Grpc::new(VecCodec::default());
            let response = grpc_service.unary(grpc_handler, request).await;
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
        .get_all_bin(OAK_LABEL_GRPC_METADATA_KEY)
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

/// [`GrpcRequestHandler`] handles gRPC requests and generates gRPC responses.
#[derive(Clone)]
struct GrpcRequestHandler {
    /// Reference to a Runtime that corresponds to the Node that created a gRPC server pseudo-Node.
    runtime: RuntimeProxy,
    /// Channel handle used for writing gRPC invocations.
    writer: oak_abi::Handle,
    /// Name of the gRPC method that should be invoked.
    method_name: String,
    metadata_map: MetadataMap,
}

impl UnaryService<Vec<u8>> for GrpcRequestHandler {
    type Response = Vec<u8>;
    type Future = BoxFuture<tonic::Response<Self::Response>, tonic::Status>;

    fn call(&mut self, request: tonic::Request<Vec<u8>>) -> Self::Future {
        let handler = self.clone();

        let oak_label_result = get_oak_label(&self.metadata_map);

        let metrics_data = handler.runtime.metrics_data();
        let future = async move {
            debug!("Processing gRPC request: {:?}", request);
            metrics_data
                .grpc_server_metrics
                .grpc_server_started_total
                .with_label_values(&[&handler.method_name])
                .inc();
            let timer = metrics_data
                .grpc_server_metrics
                .grpc_server_handled_latency_seconds
                .with_label_values(&[&handler.method_name])
                .start_timer();

            let oak_label = oak_label_result?;
            debug!("gRPC Oak Label: {:?}", oak_label);

            // Create a gRPC request.
            // TODO(#953): Add streaming support.
            let grpc_request = GrpcRequest {
                method_name: handler.method_name.to_string(),
                req_msg: request.into_inner(),
                last: true,
            };

            let response = handler
                // Handle a gRPC request and send it into the Runtime.
                .handle_grpc_request(grpc_request, &oak_label)
                // Read a gRPC response from the Runtime.
                .and_then(|response_reader| handler.handle_grpc_response(response_reader))
                // Convert an error to a gRPC error status without sending clients descriptions for
                // internal errors.
                // Errors are logged inside inside [`GrpcRequestHandler::handle_grpc_request`] and
                // [`GrpcRequestHandler::handle_grpc_response`].
                .map_err(|()| tonic::Status::new(tonic::Code::Internal, ""))?;

            // Send a gRPC response back to the client.
            debug!("Sending gRPC response: {:?}", response);
            timer.observe_duration();
            match response.status {
                None => Ok(tonic::Response::new(response.rsp_msg)),
                Some(status) if status.code == oak_abi::proto::google::rpc::Code::Ok as i32 => {
                    Ok(tonic::Response::new(response.rsp_msg))
                }
                Some(status) => Err(to_tonic_status(status)),
            }
        };

        Box::pin(future)
    }
}

impl GrpcRequestHandler {
    fn new(
        runtime: RuntimeProxy,
        writer: oak_abi::Handle,
        method_name: String,
        metadata_map: MetadataMap,
    ) -> Self {
        Self {
            runtime,
            writer,
            method_name,
            metadata_map,
        }
    }

    /// Handles a gRPC request, forwards it to a temporary channel and sends handles for this
    /// channel to the [`GrpcRequestHandler::writer`].
    /// Returns an [`oak_abi::Handle`] for reading a gRPC response from.
    fn handle_grpc_request(
        &self,
        request: GrpcRequest,
        label: &Label,
    ) -> Result<oak_abi::Handle, ()> {
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

        // Create an invocation message and attach the method-invocation specific channels to it.
        //
        // This message should be in sync with the [`oak::grpc::Invocation`] from the Oak SDK:
        // the order of the `request_reader` and `response_writer` must be consistent.
        let invocation = crate::NodeMessage {
            data: vec![],
            handles: vec![request_reader, response_writer],
        };

        // Serialize gRPC request into a message.
        let mut message = crate::NodeMessage {
            data: vec![],
            handles: vec![],
        };
        request.encode(&mut message.data).map_err(|error| {
            error!("Couldn't serialize a GrpcRequest message: {}", error);
        })?;

        // Send a message to the temporary channel.
        self.runtime
            .channel_write(request_writer, message)
            .map_err(|error| {
                error!(
                    "Couldn't write a message to the temporary channel: {:?}",
                    error
                );
            })?;

        // Send an invocation message (with attached handles) to the Oak Node.
        self.runtime
            .channel_write(self.writer, invocation)
            .map_err(|error| {
                error!("Couldn't write a gRPC invocation message: {:?}", error);
            })?;

        Ok(response_reader)
    }

    /// Processes a gRPC response from a channel represented by `response_reader` and returns an
    /// HTTP response body.
    fn handle_grpc_response(&self, response_reader: oak_abi::Handle) -> Result<GrpcResponse, ()> {
        let read_status = self
            .runtime
            .wait_on_channels(&[response_reader])
            .map_err(|error| {
                error!("Couldn't wait on the temporary gRPC channel: {:?}", error);
            })?;

        if read_status[0] == ChannelReadStatus::ReadReady {
            self.runtime
                .channel_read(response_reader)
                .map_err(|error| {
                    error!("Couldn't read from the temporary gRPC channel: {:?}", error);
                })
                .map(|message| {
                    // Return an empty HTTP body if the `message` is None.
                    message.map_or(vec![], |m| {
                        self.runtime
                            .metrics_data()
                            .grpc_server_metrics
                            .grpc_response_size_bytes
                            .with_label_values(&[&self.method_name])
                            .observe(m.data.len() as f64);
                        m.data
                    })
                })
                .and_then(|response| {
                    // Return the serialized message body.
                    GrpcResponse::decode(response.as_slice()).map_err(|error| {
                        error!("Couldn't parse the GrpcResponse message: {}", error);
                    })
                })
        } else {
            error!(
                "Couldn't read from the temporary gRPC channel: {:?}",
                read_status[0]
            );
            Err(())
        }
    }
}
