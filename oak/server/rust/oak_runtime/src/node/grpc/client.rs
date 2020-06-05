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
    io::Receiver,
    node::{
        grpc::{codec::VecCodec, invocation::Invocation},
        ConfigurationError, Node,
    },
    runtime::RuntimeProxy,
};
use log::{debug, error, info, warn};
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
    /// gRPC client to allow re-use of connection across multiple method invocations.
    grpc_client: Option<tonic::client::Grpc<tonic::transport::channel::Channel>>,
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
            grpc_client: None,
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
            debug!("Waiting for gRPC invocation");
            // Read a gRPC invocation from the [`Receiver`].
            let invocation = receiver.receive(&runtime).map_err(|error| {
                error!("Couldn't receive the invocation: {:?}", error);
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

        if self.grpc_client.is_none() {
            // Connect to an external gRPC service.
            self.grpc_client = Some(self.connect().await.map_err(|error| {
                error!("Couldn't connect to {}: {:?}", self.uri, error);
                invocation.send_error(rpc::Code::NotFound, "Service connection failed", runtime);
                OakStatus::ErrInternal
            })?);
        }
        let grpc_client = self.grpc_client.as_mut().unwrap();
        grpc_client.ready().await.map_err(|error| {
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

        // Forward the request to the external gRPC service and wait for the response(s).
        let request = tonic::Request::new(request.req_msg);
        let request_stream =
            request.map(|m| futures_util::stream::once(futures_util::future::ready(m)));
        let mut rsp_stream = match grpc_client.streaming(request_stream, path, codec).await {
            Ok(rsp_stream) => rsp_stream,
            Err(error) => {
                error!("Request to remote service failed: {}", error);
                invocation.send_error(tonic_code_to_grpc(error.code()), error.message(), runtime);
                return Ok(());
            }
        };

        let body_stream = rsp_stream.get_mut();
        loop {
            let message = body_stream.message().await.map_err(|error| {
                error!("Failed to read response: {}", error);
                invocation.send_error(rpc::Code::Internal, "Failed to read response", runtime);
                OakStatus::ErrInternal
            })?;

            if let Some(message) = message {
                let encap_rsp = GrpcResponse {
                    rsp_msg: message,
                    status: None,
                    last: false,
                };
                // Send the response back to the invocation channel.
                debug!("Sending gRPC response: {:?}", encap_rsp);
                invocation
                    .send_response(encap_rsp, &runtime)
                    .map_err(|error| {
                        error!("Couldn't send gRPC response to the invocation: {:?}", error);
                        error
                    })?;
            } else {
                debug!("No message available, close out method invocation");
                break;
            }
        }

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
