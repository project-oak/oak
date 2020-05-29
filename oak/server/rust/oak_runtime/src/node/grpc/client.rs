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
    proto::{
        google::rpc,
        oak::{application::GrpcClientConfiguration, encap::GrpcResponse},
    },
    Handle, OakStatus,
};
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
            uri,
            root_tls_certificate,
        })
    }

    /// Main loop that handles gRPC invocations from the `handle`, sends gRPC requests to an
    /// external gRPC service and writes gRPC responses back to the invocation channel.
    async fn handle_loop(&self, runtime: RuntimeProxy, handle: Handle) -> Result<(), OakStatus> {
        // Create a [`Receiver`] used for reading gRPC invocations.
        let receiver = Receiver::<Invocation>::new(handle);
        loop {
            debug!("Waiting for gRPC invocation");
            // Read a gRPC invocation from the [`Receiver`].
            let invocation = receiver.receive(&runtime).map_err(|error| {
                error!("Couldn't receive the invocation: {:?}", error);
                error
            })?;

            let result = self.process_invocation(&runtime, invocation).await;
            if let Err(status) = result {
                error!("Invocation processing failed: {:?}", status);
            }
        }
    }

    /// Process a gRPC method invocation for an external gRPC service.
    async fn process_invocation(
        &self,
        runtime: &RuntimeProxy,
        invocation: Invocation,
    ) -> Result<(), OakStatus> {
        // Receive a request from the invocation channel.
        let request = invocation.receive_request(&runtime).map_err(|error| {
            invocation.send_error(rpc::Code::Internal, "Failed to read request", runtime);
            error!(
                "Couldn't read gRPC request from the invocation: {:?}",
                error
            );
            error
        })?;
        debug!("Incoming gRPC request: {:?}", request);

        // Connect to an external gRPC service.
        let mut dispatcher = self.connect().await.map_err(|error| {
            error!("Couldn't connect to {}: {:?}", self.uri, error);
            invocation.send_error(rpc::Code::NotFound, "Service connection failed", runtime);
            OakStatus::ErrInternal
        })?;
        dispatcher.ready().await.map_err(|error| {
            error!("Service was not ready: {}", error);
            invocation.send_error(rpc::Code::NotFound, "Service not ready", runtime);
            OakStatus::ErrInternal
        })?;

        let codec = VecCodec::default();
        let path = request.method_name.parse().map_err(|error| {
            error!("Invalid URI {}: {}", request.method_name, error);
            invocation.send_error(rpc::Code::InvalidArgument, "Invalid URI", runtime);
            OakStatus::ErrInternal
        })?;

        // Send a request to the external gRPC service and wait for the response.
        let response = match dispatcher
            .unary(tonic::Request::new(request.req_msg), path, codec)
            .await
        {
            Ok(rsp) => GrpcResponse {
                rsp_msg: rsp.into_inner(),
                status: Some(from_tonic_status(tonic::Status::ok(""))),
                last: true,
            },
            Err(status) => GrpcResponse {
                rsp_msg: vec![],
                status: Some(from_tonic_status(status)),
                last: true,
            },
        };

        // Send the response back to the invocation channel.
        debug!("Sending gRPC response: {:?}", response);
        invocation
            .send_response(response, &runtime)
            .map_err(|error| {
                error!("Couldn't send gRPC response to the invocation: {:?}", error);
                error
            })?;
        Ok(())
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
            .connect()
            .await?;

        debug!("Connected to {}", self.uri);
        Ok(tonic::client::Grpc::new(connection))
    }
}

/// Oak Node implementation for the gRPC client pseudo-Node.
impl Node for GrpcClientNode {
    fn run(
        self: Box<Self>,
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
