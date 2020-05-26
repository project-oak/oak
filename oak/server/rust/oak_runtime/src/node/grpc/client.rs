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
        grpc::{codec::VecCodec, from_tonic_status, invocation::Invocation},
        ConfigurationError, Node,
    },
    runtime::RuntimeProxy,
};
use log::{debug, error, info};
use oak_abi::{
    proto::oak::{
        application::GrpcClientConfiguration,
        encap::{GrpcRequest, GrpcResponse},
    },
    Handle, OakStatus,
};
use tokio::sync::oneshot;
use tonic::transport::{Certificate, Channel, ClientTlsConfig, Uri};

/// Struct that represents a gRPC client pseudo-Node.
pub struct GrpcClientNode {
    /// Pseudo-Node name.
    node_name: String,
    /// Handler that sends gRPC requests to an external gRPC service and returns gRPC responses.
    handler: GrpcRequestHandler,
}

/// Checks if URI contains the "Host" element.
fn check_uri(uri: &Uri) -> Result<(), ConfigurationError> {
    uri.authority()
        .filter(|authority| !authority.host().is_empty())
        .map(|_| ())
        .ok_or(ConfigurationError::NoHostElement)
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
        Ok(Self {
            node_name: node_name.to_string(),
            handler: GrpcRequestHandler::new(uri, root_tls_certificate),
        })
    }

    /// Main loop that handles gRPC invocations from the `handle`, sends gRPC requests to an
    /// external gRPC service and writes gRPC responses back to the invocation channel.
    async fn handle_loop(
        &mut self,
        runtime: RuntimeProxy,
        handle: Handle,
    ) -> Result<(), OakStatus> {
        // Create a [`Receiver`] used for reading gRPC invocations.
        let receiver = Receiver::<Invocation>::new(handle);
        loop {
            debug!("Waiting for gRPC invocations");
            // Read a gRPC invocation from the [`Receiver`].
            let invocation = receiver.receive(&runtime).map_err(|error| {
                error!("Couldn't receive the invocation: {:?}", error);
                error
            })?;

            // Receive a request from the invocation channel.
            let request = invocation.receive_request(&runtime).map_err(|error| {
                error!(
                    "Couldn't receive gRPC request from the invocation: {:?}",
                    error
                );
                error
            })?;
            debug!("Incoming gRPC request: {:?}", request);

            // Send an unary request to an external gRPC service and wait for the response.
            let response = self.handler.unary_request(request).await.map_err(|error| {
                error!("Couldn't send gRPC request: {:?}", error);
                error
            })?;

            // Send a response back to the invocation channel.
            debug!("Sending gRPC response: {:?}", response);
            invocation
                .send_response(response, &runtime)
                .map_err(|error| {
                    error!("Couldn't send gRPC response to the invocation: {:?}", error);
                    error
                })?;
        }
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
}

/// Sends gRPC requests to an external gRPC service and returns gRPC responses.
struct GrpcRequestHandler {
    /// The URI component of a gRPC server endpoint. Must contain the "Host" element.
    /// https://docs.rs/tonic/0.2.1/tonic/transport/struct.Uri.html
    uri: Uri,
    /// Loaded PEM encoded X.509 TLS root certificate file used to authenticate an external gRPC
    /// service.
    root_tls_certificate: Certificate,
    /// A gRPC client dispatcher that wraps a gRPC connection and encodes/decodes messages via a
    /// provided codec. The value is assigned using [`GrpcRequestHandler::connect`] upon receiving
    /// the first gRPC request.
    dispatcher: Option<tonic::client::Grpc<tonic::transport::channel::Channel>>,
}

impl GrpcRequestHandler {
    fn new(uri: Uri, root_tls_certificate: Certificate) -> Self {
        Self {
            uri,
            root_tls_certificate,
            dispatcher: None,
        }
    }

    /// Creates a TLS connection to an external gRPC service.
    async fn connect(&mut self) -> Result<(), OakStatus> {
        debug!("Connecting to {}", self.uri);

        // Create a TLS configuration.
        let tls_config = ClientTlsConfig::new().ca_certificate(self.root_tls_certificate.clone());

        // Connect to a remote gRPC service.
        let connection = Channel::builder(self.uri.clone())
            .tls_config(tls_config)
            .connect()
            .await
            .map_err(|error| {
                error!("Couldn't connect to {}: {:?}", self.uri, error);
                OakStatus::ErrInternal
            })?;

        self.dispatcher = Some(tonic::client::Grpc::new(connection));
        debug!("Connected to {}", self.uri);
        Ok(())
    }

    /// Checks whether the [`GrpcRequestHandler::dispatcher`] is able to accept new requests.
    async fn ready(&mut self) -> Result<(), OakStatus> {
        self.dispatcher
            .as_mut()
            .expect("Handler is not connected to a gRPC service")
            .ready()
            .await
            .map_err(|error| {
                error!("Service was not ready: {}", error);
                OakStatus::ErrInternal
            })?;
        Ok(())
    }

    /// Sends an unary gRPC request wrapped in [`GrpcResponse`] to an external gRPC service.
    async fn unary_request(&mut self, request: GrpcRequest) -> Result<GrpcResponse, OakStatus> {
        // Connect to an external gRPC service.
        self.connect().await?;
        self.ready().await?;

        let codec = VecCodec::default();
        let path = request.method_name.parse().map_err(|error| {
            error!("Invalid URI {}: {}", request.method_name, error);
            OakStatus::ErrInternal
        })?;

        // Send gRPC request and wait for the response.
        self.dispatcher
            .as_mut()
            .expect("Handler is not connected to a gRPC service")
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
