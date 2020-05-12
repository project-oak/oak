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

use crate::{
    io::Receiver,
    node::{
        grpc::{codec::VecCodec, invocation::Invocation},
        Node,
    },
    runtime::RuntimeProxy,
};
use log::{debug, error, info, warn};
use oak_abi::{
    proto::oak::encap::{GrpcRequest, GrpcResponse},
    Handle, OakStatus,
};
use std::{thread, time::Duration};
use tonic::transport::{Certificate, Channel, ClientTlsConfig, Uri};

/// Struct that represents a gRPC client pseudo-Node.
pub struct GrpcClientNode {
    /// Pseudo-Node name.
    node_name: String,
    /// The URI component of a gRPC server endpoint. Must contain the "Host" element.
    /// https://docs.rs/tonic/0.2.1/tonic/transport/struct.Uri.html
    uri: Uri,
    // Loaded PEM encoded X.509 TLS root certificate file used to authenticate an external gRPC
    // service.
    root_tls_certificate: Certificate,
}

impl GrpcClientNode {
    /// Creates a new [`GrpcClientNode`] instance, but does not start it.
    pub fn new(node_name: &str, uri: Uri, root_tls_certificate: Certificate) -> Self {
        Self {
            node_name: node_name.to_string(),
            uri,
            root_tls_certificate,
        }
    }

    /// Main loop that handles gRPC invocations from the `handle`, sends gRPC requests to an
    /// external gRPC service and writes gRPC responses back to the invocation channel.
    async fn handle_loop(&self, runtime: RuntimeProxy, handle: Handle) -> Result<(), OakStatus> {
        // Connect to an external gRPC service.
        let mut handler = self.connect().await?;

        // Create a [`Receiver`] used for reading gRPC invocations.
        let receiver = Receiver::<Invocation>::new(handle);
        loop {
            // Read a gRPC invocation from the [`Receiver`].
            let invocation = receiver.receive(&runtime)?;

            // Receive a request from the invocation channel.
            let request = invocation.receive_request(&runtime)?;
            debug!("Incoming gRPC request: {:?}", request);

            // Send an unary request to an external gRPC service and wait for the response.
            let response = handler.unary_request(request).await?;

            // Send a response back to the invocation channel.
            debug!("Sending gRPC response: {:?}", response);
            invocation.send_response(response, &runtime)?;
        }
    }

    // Creates a TLS connection to an external gRPC service.
    async fn connect(&self) -> Result<GrpcRequestHandler, OakStatus> {
        debug!("Connecting to {}", self.uri);

        // Create a TLS configuration.
        let tls_config = ClientTlsConfig::new().ca_certificate(self.root_tls_certificate.clone());

        // Connect to a remote gRPC service.
        let connection = Channel::builder(self.uri.clone())
            .tls_config(tls_config)
            .connect()
            .await
            .map_err(|error| {
                warn!("Couldn't connect to {}: {:?}", self.uri, error);
                OakStatus::ErrInternal
            })?;

        debug!("Connected to {}", self.uri);
        Ok(GrpcRequestHandler::new(connection))
    }
}

/// Oak Node implementation for the gRPC client pseudo-Node.
impl Node for GrpcClientNode {
    fn run(self: Box<Self>, runtime: RuntimeProxy, handle: Handle) {
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
        let result = async_runtime.block_on(self.handle_loop(runtime, handle));
        info!(
            "{}: Exiting gRPC client pseudo-Node thread {:?}",
            self.node_name, result
        );
    }
}

/// Sends gRPC requests to an external gRPC service and returns gRPC responses.
struct GrpcRequestHandler {
    /// A gRPC client dispatcher that wraps a gRPC connection and encodes/decodes messages via a
    /// provided codec.
    dispatcher: tonic::client::Grpc<tonic::transport::channel::Channel>,
}

impl GrpcRequestHandler {
    fn new(connection: tonic::transport::channel::Channel) -> Self {
        Self {
            dispatcher: tonic::client::Grpc::new(connection),
        }
    }

    /// Checks whether the [`GrpcRequestHandler::dispatcher`] is able to accept new requests.
    async fn ready(&mut self) -> Result<(), OakStatus> {
        self.dispatcher.ready().await.map_err(|error| {
            error!("Service was not ready: {}", error);
            OakStatus::ErrInternal
        })?;
        Ok(())
    }

    /// Sends an unary gRPC request wrapped in [`GrpcResponse`] to an external gRPC service.
    async fn unary_request(&mut self, request: GrpcRequest) -> Result<GrpcResponse, OakStatus> {
        self.ready().await?;
        let codec = VecCodec::default();
        let path = request.method_name.parse().map_err(|error| {
            error!("Invalid URI {}: {}", request.method_name, error);
            OakStatus::ErrInternal
        })?;

        self.dispatcher
            .unary(tonic::Request::new(request.req_msg), path, codec)
            .await
            .map(|response| GrpcResponse {
                rsp_msg: response.into_inner(),
                status: Some(from_tonic_status(tonic::Status::ok(""))),
                last: true,
            })
            .or_else(|status| {
                Ok(GrpcResponse {
                    rsp_msg: vec![],
                    status: Some(from_tonic_status(status)),
                    last: true,
                })
            })
    }
}

/// Converts [`tonic::Status`] to [`oak_abi::proto::google::rpc::Status`].
fn from_tonic_status(status: tonic::Status) -> oak_abi::proto::google::rpc::Status {
    oak_abi::proto::google::rpc::Status {
        code: status.code() as i32,
        message: status.message().to_string(),
        details: vec![prost_types::Any {
            // `type_url` parameter is not used by Oak Nodes.
            type_url: "".to_string(),
            // Request status details that have been sent back by an external gRPC service, are
            // propagated to an Oak Node that has created this request.
            value: status.details().to_vec(),
        }],
    }
}
