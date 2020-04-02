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

use oak::grpc::GrpcRequest;
use oak_abi::{ChannelReadStatus, OakStatus};

use crate::runtime::RuntimeProxy;
use crate::{pretty_name_for_thread, Handle};

pub struct GrpcServerNode {
    config_name: String,
    runtime: RuntimeProxy,
    writer: Handle,
    thread_handle: Option<JoinHandle<()>>,
    address: SocketAddr,
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

        // Create gRPC request from HTTP body.
        Self::decode_grpc_request(grpc_method, &http_body)
            .and_then(|request| {
                // Process a gRPC request and send it into the Runtime.
                self.process_request(request)
                    .and_then(|response_reader| {
                        // Read a gRPC response from the Runtime.
                        self.process_response(response_reader)
                            .and_then(|body| {
                                // Send gRPC response back to the HTTP client.
                                Ok(Self::http_response(http::StatusCode::OK, body))
                            })
                            .or_else(|error| {
                                error!("Couldn't process gRPC response: {}", error);
                                Ok(Self::http_response(
                                    http::StatusCode::INTERNAL_SERVER_ERROR,
                                    vec![],
                                ))
                            })
                    })
                    .or_else(|error| {
                        error!("Couldn't process gRPC request: {}", error);
                        Ok(Self::http_response(
                            http::StatusCode::INTERNAL_SERVER_ERROR,
                            vec![],
                        ))
                    })
            })
            .or_else(|error| {
                error!("Couldn't decode gRPC request: {}", error);
                Ok(Self::http_response(
                    http::StatusCode::BAD_REQUEST,
                    // Return an error explanation in an HTTP response.
                    error.chars().map(|c| c as u8).collect(),
                ))
            })
    }

    /// Creates a gRPC request from `grpc_method` and an `http_body`.
    fn decode_grpc_request(
        grpc_method: &str,
        http_body: &dyn hyper::body::Buf,
    ) -> Result<GrpcRequest, String> {
        let grpc_body = protobuf::parse_from_bytes::<Any>(http_body.bytes())
            .map_err(|error| format!("Failed to parse GrpcRequest {}", error))?;

        oak::grpc::encap_request(&grpc_body, None, grpc_method)
            .ok_or("Failed to parse Protobuf message".to_string())
    }

    /// Creates an HTTP response message.
    fn http_response(status: http::StatusCode, body: Vec<u8>) -> hyper::Response<hyper::Body> {
        let mut response = hyper::Response::new(hyper::Body::from(body));
        *response.status_mut() = status;
        response
    }

    /// Processes a gRPC request, forwards it a temporary channel and sends handles for this channel
    /// to the `self.writer`.
    /// Returns a channel handle for reading a gRPC response.
    fn process_request(&self, request: GrpcRequest) -> Result<Handle, String> {
        // Create a pair of temporary channels to pass the request to the Oak node and to receive
        // the response.
        let (request_writer, request_reader) = self
            .runtime
            .channel_create(&oak_abi::label::Label::public_trusted());
        let (response_writer, response_reader) = self
            .runtime
            .channel_create(&oak_abi::label::Label::public_trusted());

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
            .map_err(|error| format!("Couldn't to serialize a GrpcRequest message: {}", error))?;

        // Send a message to the temporary channel that will be read by the Oak node.
        self.runtime
            .channel_write(request_writer, message)
            .map_err(|error| {
                format!(
                    "Couldn't write a message to the terporary gRPC server channel: {:?}",
                    error
                )
            })?;

        // Send an invocation message (with attached handles) to the Oak node.
        self.runtime
            .channel_write(self.writer, invocation)
            .map_err(|error| format!("Couldn't write a gRPC invocation message: {:?}", error))?;

        Ok(response_reader)
    }

    /// Processes a gRPC response from a channel represented by `response_reader` and returns an
    /// HTTP response body.
    fn process_response(&self, response_reader: Handle) -> Result<Vec<u8>, String> {
        let read_status = self
            .runtime
            .wait_on_channels(&[Some(response_reader)])
            .map_err(|error| format!("Couldn't wait on the temporary gRPC channel: {:?}", error))?;

        if read_status[0] == ChannelReadStatus::ReadReady {
            self.runtime
                .channel_read(response_reader)
                .map_err(|error| format!("Couldn't read temporary gRPC channel: {:?}", error))
                .map(|message| {
                    // Return an empty HTTP body is the `message` is None.
                    message.map_or(vec![], |m| m.data)
                })
        } else {
            Err(format!("Couldn't read channel: {:?}", read_status[0]))
        }
    }
}

/// Oak Node implementation for the gRPC server.
impl super::Node for GrpcServerNode {
    fn start(&mut self) -> Result<(), OakStatus> {
        let server = self.clone();
        // TODO(#770): Use `std::thread::Builder` and give a name to this thread.
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
