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

use futures_executor::block_on;
use log::{error, info, warn};
use protobuf::{well_known_types::Any, Message};
use std::{
    fmt::{self, Display, Formatter},
    net::SocketAddr,
    thread::{self, JoinHandle},
};

use oak::grpc::{encap_request, GrpcRequest};
use oak_abi::{
    ChannelReadStatus,
    label::Label,
    OakStatus
};

use crate::{
    Handle,
    pretty_name_for_thread,
    runtime::RuntimeProxy,
};

pub struct GrpcServerNode {
    config_name: String,
    runtime: RuntimeProxy,
    writer: Handle,
    thread_handle: Option<JoinHandle<()>>,
    address: SocketAddr,
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
        Self::new(
            &self.config_name,
            self.runtime.clone(),
            self.writer,
            self.address.clone(),
        )
    }
}

impl Display for GrpcServerNode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "GrpcServerNode({})", self.config_name)
    }
}

impl GrpcServerNode {
    /// Creates a new [`GrpcServerNode`] instance, but does not start it.
    pub fn new(
        config_name: &str,
        runtime: RuntimeProxy,
        writer: Handle,
        address: SocketAddr,
    ) -> Self {
        Self {
            config_name: config_name.to_string(),
            runtime,
            writer,
            thread_handle: None,
            address: address,
        }
    }

    /// Processes an incoming `http_request`, decodes a gRPC request
    async fn serve(
        &self,
        http_request: hyper::Request<hyper::Body>,
    ) -> Result<hyper::Response<hyper::Body>, hyper::Error> {
        // Parse HTTP header.
        let grpc_method = http_request.uri().path();

        // Aggregate the data buffers from an HTTP body asynchronously.
        let http_body = hyper::body::aggregate(http_request)
            .await
            .map_err(|error| {
                warn!("Couldn't aggregate request body: {}", error);
                error
            })?;

        // Create a gRPC request from an HTTP body.
        Self::decode_grpc_request(grpc_method, &http_body)
            // Process a gRPC request and send it into the Runtime.
            .and_then(|request| self.process_request(request))
            // Read a gRPC response from the Runtime.
            .and_then(|response_reader| self.process_response(response_reader))
            // Send gRPC response back to the HTTP client.
            .and_then(|body| Ok(Self::http_response(http::StatusCode::OK, body)))
            // Convert an error to an HTTP response with a corresponding error status.
            .or_else(|error| Ok(Self::http_response(error.into(), vec![])))
    }

    /// Creates a gRPC request from a `grpc_method` and an `http_body`.
    fn decode_grpc_request(
        grpc_method: &str,
        http_body: &dyn hyper::body::Buf,
    ) -> Result<GrpcRequest, GrpcServerError> {
        let grpc_body = protobuf::parse_from_bytes::<Any>(http_body.bytes())
            .map_err(|error| {
                error!("Failed to parse GrpcRequest {}", error);
                GrpcServerError::ProtobufParsingError
            })?;

        encap_request(&grpc_body, None, grpc_method)
            .ok_or_else(|| {
                error!("Failed to parse Protobuf message");
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
    /// channel to the `self.writer`.
    /// Returns a channel handle for reading a gRPC response.
    fn process_request(&self, request: GrpcRequest) -> Result<Handle, GrpcServerError> {
        // Create a pair of temporary channels to pass the gRPC request and to receive the response.
        let (request_writer, request_reader) = self
            .runtime
            .channel_create(&Label::public_trusted());
        let (response_writer, response_reader) = self
            .runtime
            .channel_create(&Label::public_trusted());

        // Create an invocation message and attach the method-invocation specific channels to it.
        let invocation = crate::Message {
            data: vec![],
            channels: vec![request_reader, response_writer],
        };

        // Serialize gRPC request into a message.
        let message = crate::Message {
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
                error!("Couldn't write a message to the terporary channel: {:?}", error);
                GrpcServerError::RequestProcessingError
            })?;

        // Send an invocation message (with attached handles) to the Oak node.
        self.runtime
            .channel_write(self.writer, invocation)
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
                    error!("Couldn't read temporary gRPC channel: {:?}", error);
                    GrpcServerError::ResponseProcessingError
                })
                .map(|message| {
                    // Return an empty HTTP body if the `message` is None.
                    message.map_or(vec![], |m| m.data)
                })
        } else {
            error!("Couldn't read channel: {:?}", read_status[0]);
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
                let service = hyper::service::make_service_fn(move |_| async move {
                    Ok::<_, hyper::Error>(hyper::service::service_fn(move |req| {
                        server.clone().serve(req)
                    }))
                });

                let result = block_on(hyper::Server::bind(&server.address).serve(service));
                info!(
                    "{} LOG: exiting gRPC server node thread {:?}",
                    pretty_name, result
                );
                server.runtime.exit_node();
            })
            .expect("failed to spawn thread");
        self.thread_handle = Some(thread_handle);
        Ok(())
    }

    fn stop(&mut self) {
        if let Some(join_handle) = self.thread_handle.take() {
            if let Err(err) = join_handle.join() {
                error!("error while stopping gRPC server node: {:?}", err);
            }
        }
    }
}
