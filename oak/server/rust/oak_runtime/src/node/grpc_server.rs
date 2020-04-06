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

use log::{error, info, warn};
use protobuf::{well_known_types::Any, Message};
use std::{
    fmt::{self, Display, Formatter},
    net::SocketAddr,
    thread::{self, JoinHandle},
};

use oak::grpc::{encap_request, GrpcRequest};
use oak_abi::{label::Label, ChannelReadStatus, OakStatus};

use crate::{pretty_name_for_thread, runtime::RuntimeProxy, Handle};

/// Struct that represents a gRPC server pseudo-node.
///
/// For each gRPC request from a client, gRPC server pseudo-node creates a pair of temporary
/// channels (to write a request to and to read a response from) and passes corresponding handles to
/// the [`GrpcServerNode::channel_writer`].
pub struct GrpcServerNode {
    /// Pseudo-node name that corresponds to an entry from the
    /// [`oak_runtime::proto::ApplicationConfiguration`].
    config_name: String,
    /// Reference to a Runtime that corresponds to a node that created a gRPC server pseudo-node.
    runtime: RuntimeProxy,
    /// Server address to listen client requests on.
    address: SocketAddr,
    /// Channel handle used for reading a [`GrpcServerNode::channel_writer`] once the gRPC server
    /// pseudo-node has started.
    initial_reader: Handle,
    /// Channel handle used for writing invocations.
    channel_writer: Option<Handle>,
    /// Thread handle that corresponds to a thread running a gRPC server pseudo-node.
    thread_handle: Option<JoinHandle<()>>,
}

#[derive(Debug)]
enum GrpcServerError {
    ProtobufParsingError,
    RequestProcessingError,
    ResponseProcessingError,
}

impl Into<http::StatusCode> for GrpcServerError {
    fn into(self) -> http::StatusCode {
        match self {
            Self::ProtobufParsingError => http::StatusCode::BAD_REQUEST,
            Self::RequestProcessingError => http::StatusCode::INTERNAL_SERVER_ERROR,
            Self::ResponseProcessingError => http::StatusCode::INTERNAL_SERVER_ERROR,
        }
    }
}

/// Clone implementation without `thread_handle` copying to pass the node to other threads.
impl Clone for GrpcServerNode {
    fn clone(&self) -> Self {
        Self {
            config_name: self.config_name.to_string(),
            runtime: self.runtime.clone(),
            address: self.address.clone(),
            initial_reader: self.initial_reader,
            channel_writer: self.channel_writer,
            thread_handle: None,
        }
    }
}

impl Display for GrpcServerNode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "GrpcServerNode({})", self.config_name)
    }
}

impl GrpcServerNode {
    /// Creates a new [`GrpcServerNode`] instance, but does not start it.
    ///
    /// `channel_writer` and `thread_handle` are initialized with `None`, because they will receive
    /// their values after the gRPC server pseudo-node has started and a separate thread was
    /// initialized.
    pub fn new(
        config_name: &str,
        runtime: RuntimeProxy,
        address: SocketAddr,
        initial_reader: Handle,
    ) -> Self {
        Self {
            config_name: config_name.to_string(),
            runtime,
            address: address,
            initial_reader,
            channel_writer: None,
            thread_handle: None,
        }
    }

    /// Reads a [`Handle`] from a channel specified by [`GrpcServerNode::initial_reader`].
    /// Returns an error if couldn't read from the channel or if received a wrong number of handles
    /// (not equal to 1).
    fn init_channel_writer(&self) -> Result<Handle, OakStatus> {
        let read_status = self
            .runtime
            .wait_on_channels(&[Some(self.initial_reader)])
            .map_err(|error| {
                error!("Couldn't wait on the initial reader handle: {:?}", error);
                OakStatus::ErrInternal
            })?;

        if read_status[0] == ChannelReadStatus::ReadReady {
            self.runtime
                .channel_read(self.initial_reader)
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
                            if m.channels.len() == 1 {
                                Ok(m.channels[0])
                            } else {
                                error!(
                                    "gRPC server pseudo-node should receive a single `writer` handle, found {}",
                                    m.channels.len()
                                );
                                Err(OakStatus::ErrInternal)
                            }
                        })
                })
        } else {
            error!("Couldn't read channel: {:?}", read_status[0]);
            Err(OakStatus::ErrInternal)
        }
    }

    /// Processes an HTTP request from a client and sends an HTTP response back.
    async fn serve(
        &self,
        http_request: hyper::Request<hyper::Body>,
    ) -> Result<hyper::Response<hyper::Body>, hyper::Error> {
        // Parse HTTP header.
        let http_request_path = http_request.uri().path().to_string();

        // Aggregate the data buffers from an HTTP body asynchronously.
        let http_request_body = hyper::body::aggregate(http_request)
            .await
            .map_err(|error| {
                warn!("Couldn't aggregate request body: {}", error);
                error
            })?;

        // Create a gRPC request from an HTTP body.
        Self::decode_grpc_request(&http_request_path, &http_request_body)
            // Process a gRPC request and send it into the Runtime.
            .and_then(|request| self.process_request(request))
            // Read a gRPC response from the Runtime.
            .and_then(|response_reader| self.process_response(response_reader))
            // Send gRPC response back to the HTTP client.
            .map(|body| Self::http_response(http::StatusCode::OK, body))
            // Convert an error to an HTTP response with a corresponding error status.
            .or_else(|error| Ok(Self::http_response(error.into(), vec![])))
    }

    /// Creates a [`GrpcRequest`] instance from a `http_request_path` and an `http_request_body`.
    fn decode_grpc_request(
        http_request_path: &str,
        http_request_body: &dyn hyper::body::Buf,
    ) -> Result<GrpcRequest, GrpcServerError> {
        // Parse an HTTP request body as a [`protobuf::well_known_types::Any`] message.
        let grpc_request_body = protobuf::parse_from_bytes::<Any>(http_request_body.bytes())
            .map_err(|error| {
                error!("Failed to parse Protobuf message {}", error);
                GrpcServerError::ProtobufParsingError
            })?;

        // Create a gRPC request.
        encap_request(&grpc_request_body, None, http_request_path).ok_or_else(|| {
            error!("Failed to create a GrpcRequest");
            GrpcServerError::ProtobufParsingError
        })
    }

    /// Creates an HTTP response message.
    fn http_response(status: http::StatusCode, body: Vec<u8>) -> hyper::Response<hyper::Body> {
        let mut response = hyper::Response::new(hyper::Body::from(body));
        *response.status_mut() = status;
        response
    }

    /// Processes a gRPC request, forwards it to a temporary channel and sends handles for this
    /// channel to the [`GrpcServerNode::channel_writer`].
    /// Returns a [`Handle`] for reading a gRPC response from.
    fn process_request(&self, request: GrpcRequest) -> Result<Handle, GrpcServerError> {
        // Create a pair of temporary channels to pass the gRPC request and to receive the response.
        let (request_writer, request_reader) =
            self.runtime.channel_create(&Label::public_trusted());
        let (response_writer, response_reader) =
            self.runtime.channel_create(&Label::public_trusted());

        // Create an invocation message and attach the method-invocation specific channels to it.
        //
        // This message should be in sync with the [`oak::grpc::Invocation`] from the Oak SDK:
        // the order of the `request_reader` and `response_writer` must be consistent.
        let invocation = crate::Message {
            data: vec![],
            channels: vec![request_reader, response_writer],
        };

        // Serialize gRPC request into a message.
        let mut message = crate::Message {
            data: vec![],
            channels: vec![],
        };
        request
            .write_to_writer(&mut message.data)
            .map_err(|error| {
                error!("Couldn't serialize a GrpcRequest message: {}", error);
                GrpcServerError::RequestProcessingError
            })?;

        // Send a message to the temporary channel.
        self.runtime
            .channel_write(request_writer, message)
            .map_err(|error| {
                error!(
                    "Couldn't write a message to the temporary channel: {:?}",
                    error
                );
                GrpcServerError::RequestProcessingError
            })?;

        // Send an invocation message (with attached handles) to the Oak node.
        self.runtime
            .channel_write(
                self.channel_writer.expect("Node writer wasn't initialized"),
                invocation,
            )
            .map_err(|error| {
                error!("Couldn't write a gRPC invocation message: {:?}", error);
                GrpcServerError::RequestProcessingError
            })?;

        Ok(response_reader)
    }

    /// Processes a gRPC response from a channel represented by `response_reader` and returns an
    /// HTTP response body.
    fn process_response(&self, response_reader: Handle) -> Result<Vec<u8>, GrpcServerError> {
        let read_status = self
            .runtime
            .wait_on_channels(&[Some(response_reader)])
            .map_err(|error| {
                error!("Couldn't wait on the temporary gRPC channel: {:?}", error);
                GrpcServerError::ResponseProcessingError
            })?;

        if read_status[0] == ChannelReadStatus::ReadReady {
            self.runtime
                .channel_read(response_reader)
                .map_err(|error| {
                    error!("Couldn't read from a temporary gRPC channel: {:?}", error);
                    GrpcServerError::ResponseProcessingError
                })
                .map(|message| {
                    // Return an empty HTTP body if the `message` is None.
                    message.map_or(vec![], |m| m.data)
                })
        } else {
            error!(
                "Couldn't read from a temporary gRPC channel: {:?}",
                read_status[0]
            );
            Err(GrpcServerError::ResponseProcessingError)
        }
    }
}

/// Oak Node implementation for the gRPC server.
impl super::Node for GrpcServerNode {
    fn start(&mut self) -> Result<(), OakStatus> {
        let server = self.clone();
        let thread_handle = thread::Builder::new()
            .name(self.to_string())
            .spawn(move || {
                let pretty_name = pretty_name_for_thread(&thread::current());

                // Receive a `writer` handle used to pass handles for temporary channels.
                server
                    .init_channel_writer()
                    .expect("Couldn't initialialize node writer");

                // Initialize a function that creates a separate instance on the `server` for each
                // HTTP request.
                //
                // TODO(#813): Remove multiple `clone` calls by either introducing `Arc<Mutex<T>>`
                // or not using Hyper (move to more simple single-threaded server).
                let generator_server = server.clone();
                let service = hyper::service::make_service_fn(move |_| {
                    let connection_server = generator_server.clone();
                    async move {
                        Ok::<_, hyper::Error>(hyper::service::service_fn(move |req| {
                            let request_server = connection_server.clone();
                            async move { request_server.serve(req).await }
                        }))
                    }
                });

                // Start the HTTP server.
                let mut tokio_runtime =
                    tokio::runtime::Runtime::new().expect("Couldn't create Tokio runtime");
                let result =
                    tokio_runtime.block_on(hyper::Server::bind(&server.address).serve(service));
                info!(
                    "{} LOG: exiting gRPC server node thread {:?}",
                    pretty_name, result
                );
                server.runtime.exit_node();
            })
            .expect("Failed to spawn thread");
        self.thread_handle = Some(thread_handle);
        Ok(())
    }

    fn stop(&mut self) {
        if let Some(join_handle) = self.thread_handle.take() {
            if let Err(err) = join_handle.join() {
                error!("Error while stopping gRPC server node: {:?}", err);
            }
        }
    }
}
