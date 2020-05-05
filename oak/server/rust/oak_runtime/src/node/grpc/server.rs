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

use hyper::service::Service;
use log::{debug, error, info, warn};
use prost::Message;
use std::{
    fmt::{self, Display, Formatter},
    net::SocketAddr,
    task::{Context, Poll},
    thread::{self, JoinHandle},
};
use tonic::{
    codec::{Codec, DecodeBuf, Decoder, EncodeBuf, Encoder},
    codegen::BoxFuture,
    server::{Grpc, UnaryService},
    transport::{Identity, NamedService},
};

use oak_abi::{
    grpc::encap_request, label::Label, proto::oak::encap::GrpcRequest, ChannelReadStatus, OakStatus,
};

use crate::{
    Handle,
    metrics::METRICS,
    node::Node,
    pretty_name_for_thread,
    runtime::RuntimeProxy,
};

/// Struct that represents a gRPC server pseudo-Node.
///
/// For each gRPC request from a client, gRPC server pseudo-Node creates a pair of temporary
/// channels (to write a request to and to read a response from) and passes corresponding handles to
/// the [`GrpcServerNode::channel_writer`].
#[derive(Clone)]
pub struct GrpcServerNode {
    /// Pseudo-Node name that corresponds to an entry from the [`ApplicationConfiguration`].
    ///
    /// [`ApplicationConfiguration`]: crate::proto::oak::application::ApplicationConfiguration
    config_name: String,
    /// Reference to a Runtime that corresponds to a Node that created a gRPC server pseudo-Node.
    runtime: RuntimeProxy,
    /// Server address to listen client requests on.
    address: SocketAddr,
    /// Loaded files containing a server TLS key and certificates.
    tls_identity: Identity,
    /// Channel handle used for reading a [`GrpcServerNode::channel_writer`] once the gRPC server
    /// pseudo-Node has started.
    initial_reader: Handle,
    /// Channel handle used for writing gRPC invocations.
    /// Is set after the [`GrpcServerNode::init_channel_writer`] is called.
    channel_writer: Option<Handle>,
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
    /// their values after the gRPC server pseudo-Node has started and a separate thread was
    /// initialized.
    pub fn new(
        config_name: &str,
        runtime: RuntimeProxy,
        address: SocketAddr,
        tls_identity: Identity,
        initial_reader: Handle,
    ) -> Self {
        Self {
            config_name: config_name.to_string(),
            runtime,
            address,
            tls_identity,
            initial_reader,
            channel_writer: None,
        }
    }

    /// Reads a [`Handle`] from a channel specified by [`GrpcServerNode::initial_reader`].
    /// Returns an error if couldn't read from the channel or if received a wrong number of handles
    /// (not equal to 1).
    fn init_channel_writer(&mut self) -> Result<(), OakStatus> {
        let read_status = self
            .runtime
            .wait_on_channels(&[self.initial_reader])
            .map_err(|error| {
                error!("Couldn't wait on the initial reader handle: {:?}", error);
                OakStatus::ErrInternal
            })?;

        let channel_writer = if read_status[0] == ChannelReadStatus::ReadReady {
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
                                    "gRPC server pseudo-Node should receive a single writer handle, found {}",
                                    m.channels.len()
                                );
                                Err(OakStatus::ErrInternal)
                            }
                        })
                })
        } else {
            error!("Couldn't read channel: {:?}", read_status[0]);
            Err(OakStatus::ErrInternal)
        }?;
        self.channel_writer = Some(channel_writer);

        warn!("Channel writer received: {:?}", self.channel_writer);
        Ok(())
    }

    /// Main Node worker thread.
    fn worker_thread(mut self) {
        let pretty_name = pretty_name_for_thread(&thread::current());

        // Receive a `channel_writer` handle used to pass handles for temporary channels.
        info!("{}: Waiting for a channel writer", pretty_name);
        self.init_channel_writer()
            .expect("Couldn't initialialize a channel writer");

        let handler = HttpRequestHandler {
            runtime: self.runtime.clone(),
            writer: self
                .channel_writer
                .expect("Channel writer is not initialized"),
        };

        // Handles incoming TLS connections, unpacks HTTP/2 requests and forwards them to
        // [`HttpRequestHandler::handle`].
        let server = tonic::transport::Server::builder()
            .tls_config(tonic::transport::ServerTlsConfig::new().identity(self.tls_identity))
            .add_service(handler)
            .serve(self.address);

        // Create an Async runtime for executing futures.
        // https://docs.rs/tokio/
        let mut async_runtime = tokio::runtime::Builder::new()
            // Use simple scheduler that runs all tasks on the current-thread.
            // https://docs.rs/tokio/0.2.16/tokio/runtime/index.html#basic-scheduler
            .basic_scheduler()
            // Enables the I/O driver.
            // Necessary for using net, process, signal, and I/O types on the Tokio runtime.
            .enable_io()
            .build()
            .expect("Couldn't create an Async runtime");

        // Start a gRPC server.
        info!(
            "{}: Starting a gRPC server pseudo-Node on: {}",
            pretty_name, self.address
        );
        let result = async_runtime.block_on(server);
        info!(
            "{}: Exiting gRPC server pseudo-Node thread {:?}",
            pretty_name, result
        );

        self.runtime.exit_node();
    }
}

/// Oak Node implementation for the gRPC server.
impl Node for GrpcServerNode {
    fn start(self: Box<Self>) -> Result<JoinHandle<()>, OakStatus> {
        let thread_handle = thread::Builder::new()
            .name(self.to_string())
            .spawn(move || self.worker_thread())
            .expect("Failed to spawn thread");
        Ok(thread_handle)
    }
}

/// [`HttpRequestHandler`] handles HTTP/2 requests from a client and sends HTTP/2 responses back.
#[derive(Clone)]
struct HttpRequestHandler {
    /// Reference to a Runtime that corresponds to a node that created a gRPC server pseudo-Node.
    runtime: RuntimeProxy,
    /// Channel handle used for writing gRPC invocations.
    writer: Handle,
}

// Set a mandatory prefix for all gRPC requests processed by a gRPC pseudo-Node.
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

    // Decodes an unary gRPC request using a [`VecCodec`] and processes it with
    // [`tonic::server::Grpc::unary`] and a [`GrpcRequestHandler`].
    fn call(&mut self, request: http::Request<hyper::Body>) -> Self::Future {
        let grpc_handler = GrpcRequestHandler::new(
            self.runtime.clone(),
            self.writer,
            request.uri().path().to_string(),
        );

        let future = async move {
            debug!("Processing an HTTP/2 request: {:?}", request);
            let mut grpc_service = Grpc::new(VecCodec::default());
            let response = grpc_service.unary(grpc_handler, request).await;
            debug!("Sending an HTTP/2 response: {:?}", response);
            Ok(response)
        };

        Box::pin(future)
    }
}

/// Encapsulates [`VecEncoder`] and [`VecDecoder`] types and is used by [`tonic::server::Grpc`].
#[derive(Default)]
struct VecCodec;

impl Codec for VecCodec {
    type Encode = Vec<u8>;
    type Decode = Vec<u8>;

    type Encoder = VecEncoder;
    type Decoder = VecDecoder;

    fn encoder(&mut self) -> Self::Encoder {
        VecEncoder::default()
    }

    fn decoder(&mut self) -> Self::Decoder {
        VecDecoder::default()
    }
}

/// Custom encoder for creating [`tonic::codec::EncodeBuf`] from bytes.
#[derive(Default)]
struct VecEncoder;

impl Encoder for VecEncoder {
    type Item = Vec<u8>;
    type Error = tonic::Status;

    fn encode(&mut self, item: Self::Item, dst: &mut EncodeBuf<'_>) -> Result<(), Self::Error> {
        use bytes::BufMut;

        dst.put(&item[..]);
        Ok(())
    }
}

/// Custom decoder for extracting bytes from [`tonic::codec::DecodeBuf`].
#[derive(Default)]
struct VecDecoder;

impl Decoder for VecDecoder {
    type Item = Vec<u8>;
    type Error = tonic::Status;

    fn decode(&mut self, src: &mut DecodeBuf<'_>) -> Result<Option<Self::Item>, Self::Error> {
        use bytes::{buf::BufExt, Buf};

        let item = Vec::from(src.reader().into_inner().bytes());
        Ok(Some(item))
    }
}

/// [`GrpcRequestHandler`] handles gRPC requests and generates gRPC responses.
#[derive(Clone)]
struct GrpcRequestHandler {
    /// Reference to a Runtime that corresponds to the Node that created a gRPC server pseudo-Node.
    runtime: RuntimeProxy,
    /// Channel handle used for writing gRPC invocations.
    writer: Handle,
    /// Name of the gRPC method that should be invoked.
    method_name: String,
}

impl UnaryService<Vec<u8>> for GrpcRequestHandler {
    type Response = Vec<u8>;
    type Future = BoxFuture<tonic::Response<Self::Response>, tonic::Status>;

    fn call(&mut self, request: tonic::Request<Vec<u8>>) -> Self::Future {
        let handler = self.clone();
        let future = async move {
            debug!("Processing a gRPC request: {:?}", request);
            METRICS.grpc_requests_total.inc();
            let timer = METRICS.grpc_request_duration.start_timer();

            // Decode a gRPC request.
            let grpc_request =
                encap_request(request.get_ref(), &handler.method_name).ok_or_else(|| {
                    let warning = "Failed to parse an incoming Protobuf message";
                    warn!("{}", warning);
                    tonic::Status::new(tonic::Code::InvalidArgument, warning)
                })?;

            let response = handler
                // Handle a gRPC request and send it into the Runtime.
                .handle_grpc_request(grpc_request)
                // Read a gRPC response from the Runtime.
                .and_then(|response_reader| handler.handle_grpc_response(response_reader))
                // Convert an error to a gRPC error status without sending clients descriptions for
                // internal errors.
                // Errors are logged inside inside [`GrpcRequestHandler::handle_grpc_request`] and
                // [`GrpcRequestHandler::handle_grpc_response`].
                .map_err(|_| tonic::Status::new(tonic::Code::Internal, ""))?;

            // Send a gRPC response back to the client.
            debug!("Sending a gRPC response: {:?}", response);
            timer.observe_duration();
            Ok(tonic::Response::new(response))
        };

        Box::pin(future)
    }
}

impl GrpcRequestHandler {
    fn new(runtime: RuntimeProxy, writer: Handle, method_name: String) -> Self {
        Self {
            runtime,
            writer,
            method_name,
        }
    }

    /// Handles a gRPC request, forwards it to a temporary channel and sends handles for this
    /// channel to the [`GrpcServerNode::channel_writer`].
    /// Returns a [`Handle`] for reading a gRPC response from.
    fn handle_grpc_request(&self, request: GrpcRequest) -> Result<Handle, OakStatus> {
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
        request.encode(&mut message.data).map_err(|error| {
            error!("Couldn't serialize a GrpcRequest message: {}", error);
            OakStatus::ErrInternal
        })?;

        // Send a message to the temporary channel.
        self.runtime
            .channel_write(request_writer, message)
            .map_err(|error| {
                error!(
                    "Couldn't write a message to the temporary channel: {:?}",
                    error
                );
                error
            })?;

        // Send an invocation message (with attached handles) to the Oak Node.
        self.runtime
            .channel_write(self.writer, invocation)
            .map_err(|error| {
                error!("Couldn't write a gRPC invocation message: {:?}", error);
                error
            })?;

        Ok(response_reader)
    }

    /// Handles a gRPC response from a channel represented by `response_reader` and returns a
    /// gRPC response body.
    fn handle_grpc_response(&self, response_reader: Handle) -> Result<Vec<u8>, OakStatus> {
        let read_status = self
            .runtime
            .wait_on_channels(&[response_reader])
            .map_err(|error| {
                error!("Couldn't wait on the temporary gRPC channel: {:?}", error);
                error
            })?;

        if read_status[0] == ChannelReadStatus::ReadReady {
            self.runtime
                .channel_read(response_reader)
                .map_err(|error| {
                    error!("Couldn't read from a temporary gRPC channel: {:?}", error);
                    error
                })
                .map(|message| {
                    // Return an empty HTTP body if the `message` is None.
                    message.map_or(vec![], |m| {
                        METRICS.grpc_response_size.observe(m.data.len() as f64);
                        m.data
                    })
                })
        } else {
            error!(
                "Couldn't read from a temporary gRPC channel: {:?}",
                read_status[0]
            );
            Err(OakStatus::ErrInternal)
        }
    }
}
