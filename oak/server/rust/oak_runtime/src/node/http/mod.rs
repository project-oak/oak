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

//! HTTP server pseudo-Node that can serve as a frontend for an Oak node.
//! The server receives requests from the outside, wraps each request in
//! an invocation and sends it to the designated Oak node to be processed
//! asynchronously.

use crate::{
    io::{ReceiverExt, SenderExt},
    node::{ConfigurationError, Node},
    ChannelHalfDirection, RuntimeProxy,
};
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server, StatusCode,
};
use log::{debug, error, info, warn};
use oak_abi::{
    label::Label,
    proto::oak::{
        application::HttpServerConfiguration,
        encap::{HttpRequest, HttpResponse},
    },
    ChannelReadStatus, OakStatus,
};
use oak_io::handle::{ReadHandle, WriteHandle};
use prost::Message;
use std::{future::Future, net::SocketAddr, pin::Pin};
use tokio::sync::oneshot;

#[cfg(test)]
pub mod tests;

/// Checks that prot is not reserved (i.e., is greater than 1023).
fn check_port(address: &SocketAddr) -> Result<(), ConfigurationError> {
    if address.port() > 1023 {
        Ok(())
    } else {
        Err(ConfigurationError::IncorrectPort)
    }
}

/// Struct that represents an HTTP server pseudo-Node.
pub struct HttpServerNode {
    /// Pseudo-Node name.
    node_name: String,
    /// Server address to listen client requests on.
    address: SocketAddr,
}

impl HttpServerNode {
    /// Creates a new [`HttpServerNode`] instance, but does not start it.
    pub fn new(
        node_name: &str,
        config: HttpServerConfiguration,
    ) -> Result<Self, ConfigurationError> {
        let address = config.address.parse()?;
        check_port(&address)?;
        Ok(Self {
            node_name: node_name.to_string(),
            address,
        })
    }

    /// Reads the [`oak_abi::Handle`] for the write half of an invocation from a startup channel.
    /// Returns an error if the startup channel couldn't be read, or if the initial message
    /// is invalid (doesn't contain exactly one write handle).
    fn try_get_invocation_channel(
        runtime: &RuntimeProxy,
        startup_handle: oak_abi::Handle,
    ) -> Result<oak_abi::Handle, OakStatus> {
        // Wait until a message is available on the startup channel
        let read_status = runtime
            .wait_on_channels(&[startup_handle])
            .map_err(|error| {
                error!("Couldn't wait on the initial reader handle: {:?}", error);
                OakStatus::ErrInternal
            })?;

        // TODO(#389): Automatically generate this code.
        let invocation_channel = if read_status[0] == ChannelReadStatus::ReadReady {
            HttpServerNode::get_invocation_channel(runtime, startup_handle)
        } else {
            error!("Couldn't read channel: {:?}", read_status[0]);
            Err(OakStatus::ErrInternal)
        }?;

        info!(
            "Invocation channel write handle received: {}",
            invocation_channel
        );
        Ok(invocation_channel)
    }

    fn get_invocation_channel(
        runtime: &RuntimeProxy,
        startup_handle: oak_abi::Handle,
    ) -> Result<oak_abi::Handle, OakStatus> {
        runtime.channel_read(startup_handle)
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
                            // TODO(#1186): create an Init object and define encode/decode for it
                            // Ref: https://github.com/project-oak/oak/pull/1261#discussion_r457943479
                            if m.handles.len() == 1 {
                                let handle = m.handles[0];
                                match runtime.channel_direction(handle)? {
                                    ChannelHalfDirection::Write => Ok(handle),
                                    ChannelHalfDirection::Read => {
                                        error!(
                                            "Http server pseudo-node should receive a writer handle, found reader handle {}",
                                            handle
                                        );
                                        Err(OakStatus::ErrBadHandle)
                                    },
                                }
                            } else {
                                error!(
                                    "Http server pseudo-node should receive a single writer handle, found {}",
                                    m.handles.len()
                                );
                                Err(OakStatus::ErrInternal)
                            }
                        })
                })
    }

    // Make a server, with graceful shutdown, from the given [`HttpRequestHandler`].
    async fn make_server(
        &self,
        request_handler: HttpRequestHandler,
        notify_receiver: tokio::sync::oneshot::Receiver<()>,
    ) {
        // A `Service` is needed for every connection, so this
        // creates one from the `request_handler`.
        let make_service = make_service_fn(move |_conn| {
            let handler = request_handler.clone();
            async move {
                Ok::<_, hyper::Error>(service_fn(move |req| {
                    let handler = handler.clone();

                    async move {
                        let http_request = HttpServerNode::map_to_http_request(req).await;
                        handler.handle(http_request).await
                    }
                }))
            }
        });

        let server = Server::bind(&self.address).serve(make_service);
        let graceful_server = server.with_graceful_shutdown(async {
            // Treat notification failure the same as a notification.
            let _ = notify_receiver.await;
        });
        info!(
            "{:?}: Started HTTP server pseudo-node on port {:?}",
            std::thread::current().id(),
            &self.address.port()
        );

        // Run until asked to terminate...
        let result = graceful_server.await;
        info!("HTTP server pseudo-node terminated with {:?}", result);
    }

    // Create an instance of HttpRequest, from the given Request.
    async fn map_to_http_request(req: Request<Body>) -> HttpRequest {
        let path = req.uri().to_string();
        let method = req.method().as_str().to_string();
        let req_headers = req.headers();
        let headers = req_headers
            .into_iter()
            .map(|(key, value)| {
                let val = value.as_bytes().to_vec();
                (key.to_string(), val)
            })
            .collect();
        let body_stream = req.into_body();

        let body = hyper::body::to_bytes(body_stream)
            .await
            .expect("Error when reading request body from the connection")
            .to_vec();

        HttpRequest {
            path,
            method,
            body,
            headers,
        }
    }
}

/// Oak Node implementation for the HTTP server.
impl Node for HttpServerNode {
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        startup_handle: oak_abi::Handle,
        notify_receiver: oneshot::Receiver<()>,
    ) {
        // At start-of-day we need/expect to receive a write handle for an invocation channel
        // to use for all subsequent activity.
        info!("{}: Waiting for invocation channel", self.node_name);
        let invocation_channel =
            match HttpServerNode::try_get_invocation_channel(&runtime, startup_handle) {
                Ok(writer) => writer,
                Err(status) => {
                    error!(
                        "Failed to retrieve invocation channel write handle: {:?}",
                        status
                    );
                    return;
                }
            };
        if let Err(err) = runtime.channel_close(startup_handle) {
            error!(
                "Failed to close initial inbound channel {}: {:?}",
                startup_handle, err
            );
        }

        // Build a service to process all incoming HTTP requests.
        let generic_handler = HttpRequestHandler {
            runtime,
            invocation_channel,
        };
        let server = self.make_server(generic_handler, notify_receiver);

        // Create an Async runtime for executing futures.
        // https://docs.rs/tokio/
        // TODO(#1280): Use a single shared tokio runtime, instead of creating a new one here
        let mut async_runtime = create_async_runtime();

        // Start the HTTP server.
        info!(
            "{}: Starting HTTP server pseudo-Node on: {}",
            self.node_name, self.address
        );
        async_runtime.block_on(server);
    }
}

fn create_async_runtime() -> tokio::runtime::Runtime {
    tokio::runtime::Builder::new()
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
        .expect("Couldn't create Async runtime")
}

/// [`HttpRequestHandler`] handles HTTP requests from a client and sends HTTP responses back.
#[derive(Clone)]
struct HttpRequestHandler {
    /// Reference to the Runtime in the context of this HTTP server pseudo-Node.
    runtime: RuntimeProxy,
    /// Channel handle used for writing HTTP invocations.
    invocation_channel: oak_abi::Handle,
}

impl HttpRequestHandler {
    fn handle(
        &self,
        request: HttpRequest,
    ) -> Pin<Box<dyn Future<Output = Result<Response<Body>, OakStatus>> + Send + Sync>> {
        let handler = self.clone();
        let future = async move {
            let oak_label = get_oak_label(&request)?;
            info!(
                "handling HTTP request; request size: {} bytes, label: {:?}",
                request.body.len(),
                oak_label
            );

            debug!("inject the request into the Oak Node");
            let response = handler
                .inject_http_request(request, &oak_label)
                .map_err(|_| OakStatus::ErrInternal)?;

            Ok(response.to_response())
        };

        Box::pin(future)
    }

    fn inject_http_request(
        &self,
        request: HttpRequest,
        label: &Label,
    ) -> Result<HttpResponseIterator, ()> {
        // Create a pair of temporary channels to pass the HTTP request and to receive the
        // response.
        let pipe = Pipe::new(&self.runtime.clone(), label)?;

        // Put the HTTP request message inside the per-invocation request channel.
        pipe.insert_message(&self.runtime, request)?;

        // Send an invocation message (with attached handles) to the Oak Node.
        pipe.send_invocation(&self.runtime, self.invocation_channel)?;

        // Close all local handles except for the one that allows reading responses.
        pipe.close(&self.runtime);

        Ok(HttpResponseIterator {
            runtime: self.runtime.clone(),
            response_reader: pipe.response_reader,
        })
    }
}

// A pair of temporary channels to pass the HTTP request and to receive the response.
struct Pipe {
    request_writer: oak_abi::Handle,
    request_reader: oak_abi::Handle,
    response_writer: oak_abi::Handle,
    response_reader: oak_abi::Handle,
}

impl Pipe {
    fn new(runtime: &RuntimeProxy, label: &Label) -> Result<Self, ()> {
        // Create a channel for passing HTTP requests to the Oak node. This channel is created with
        // the label specified by the caller. This will fail if the label has a non-empty
        // integrity component.
        let (request_writer, request_reader) = runtime.channel_create(&label).map_err(|err| {
            warn!("could not create HTTP request channel: {:?}", err);
        })?;
        let (response_writer, response_reader) = runtime
            .channel_create(&Label::public_untrusted())
            .map_err(|err| {
                warn!("could not create HTTP response channel: {:?}", err);
            })?;

        Ok(Pipe {
            request_writer,
            request_reader,
            response_writer,
            response_reader,
        })
    }

    fn insert_message(&self, runtime: &RuntimeProxy, request: HttpRequest) -> Result<(), ()> {
        // Put the HTTP request message inside the per-invocation request channel.
        let sender = crate::io::Sender::new(WriteHandle {
            handle: self.request_writer,
        });
        sender.send(request, runtime).map_err(|err| {
            error!(
                "Couldn't write the request to the HTTP request channel: {:?}",
                err
            )
        })
    }

    fn send_invocation(
        &self,
        runtime: &RuntimeProxy,
        invocation_channel: oak_abi::Handle,
    ) -> Result<(), ()> {
        // Create an invocation message and attach the request specific channels to it.
        // TODO(#1186): Use a generic version of gRPC invocation, instead of serializing manually
        let invocation = crate::NodeMessage {
            data: vec![],
            handles: vec![self.request_reader, self.response_writer],
        };

        // Send an invocation message (with attached handles) to the Oak Node.
        runtime
            .channel_write(invocation_channel, invocation)
            .map_err(|error| {
                error!("Couldn't write the invocation message: {:?}", error);
            })
    }

    // Close all local handles except for the one that allows reading responses.
    fn close(&self, runtime: &RuntimeProxy) {
        if let Err(err) = runtime.channel_close(self.request_writer) {
            error!(
                "Failed to close request writer channel for invocation: {:?}",
                err
            );
        }
        if let Err(err) = runtime.channel_close(self.request_reader) {
            error!(
                "Failed to close request reader channel for invocation: {:?}",
                err
            );
        }
        if let Err(err) = runtime.channel_close(self.response_writer) {
            error!(
                "Failed to close response writer channel for invocation: {:?}",
                err
            );
        }
    }
}

// TODO(#1279): Get the label from a JSON string instead of a binary label
fn get_oak_label(req: &HttpRequest) -> Result<Label, OakStatus> {
    match req.headers.get(oak_abi::OAK_LABEL_HTTP_KEY) {
        Some(label) => Label::decode(&label[..]).map_err(|err| {
            warn!("Could not parse HTTP label: {}", err);
            OakStatus::ErrInvalidArgs
        }),
        None => {
            warn!("No HTTP label found:");
            Err(OakStatus::ErrInvalidArgs)
        }
    }
}

struct HttpResponseIterator {
    runtime: RuntimeProxy,
    response_reader: oak_abi::Handle,
}

impl HttpResponseIterator {
    fn read_response(&self) -> Result<HttpResponse, OakStatus> {
        let response_receiver = crate::io::Receiver::<HttpResponse>::new(ReadHandle {
            handle: self.response_reader,
        });
        response_receiver.receive(&self.runtime)
    }

    fn to_response(&self) -> Response<Body> {
        info!(
            "Generating response for runtime {} and reader {:?}.",
            self.runtime.node_id.0, self.response_reader
        );
        let mut response = Response::new(Body::empty());
        match self.read_response() {
            Ok(http_response) => {
                let status_code = http_response.status as u16;
                *response.body_mut() = Body::from(http_response.body);
                *response.status_mut() = StatusCode::from_u16(status_code)
                    .unwrap_or_else(|_| panic!("Error when creating status code {}", status_code));
            }
            Err(status) => {
                error!("Could not read response: {}", status);
                *response.status_mut() =
                    StatusCode::from_u16(http::status::StatusCode::INTERNAL_SERVER_ERROR.as_u16())
                        .expect("Error when creating internal error (500) status code.");
            }
        }
        response
    }
}
