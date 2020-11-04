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
    io::{ReceiverExt, Sender, SenderExt},
    node::{ConfigurationError, Node, NodePrivilege},
    proto::oak::invocation::{HttpInvocation, HttpInvocationSender},
    RuntimeProxy,
};
use core::task::{Context, Poll};
use futures_util::stream::Stream;
use http::{request::Request, response::Response};
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Server, StatusCode,
};
use log::{debug, error, info, warn};
use oak_abi::{
    label::{confidentiality_label, public_key_identity_tag, Label},
    proto::oak::application::HttpServerConfiguration,
    OakStatus,
};
use oak_io::{
    handle::{ReadHandle, WriteHandle},
    OakError, Receiver,
};
use oak_services::proto::oak::encap::{HeaderMap, HttpRequest, HttpResponse};
use std::{io, net::SocketAddr, pin::Pin};
use tokio::{
    net::{TcpListener, TcpStream},
    sync::oneshot,
};
use tokio_rustls::server::TlsStream;

use futures_util::{
    future::TryFutureExt,
    stream::{StreamExt, TryStreamExt},
};
use oak_abi::proto::oak::identity::SignedChallenge;
use prost::Message;
use tokio_rustls::TlsAcceptor;

#[cfg(test)]
pub mod tests;

// TODO(#1693): Use anyhow instead of HttpError.
#[derive(Debug)]
enum HttpError {
    ChannelOperation(String),
    HttpRequest(String),
    HttpResponse(String),
    IdentityVerification(String),
    RequestLabel(String),
}

/// Checks that port is not reserved (i.e., is greater than 1023).
fn check_port(address: &SocketAddr) -> Result<(), ConfigurationError> {
    if address.port() > 1023 {
        Ok(())
    } else {
        Err(ConfigurationError::IncorrectPort)
    }
}

/// Asynchronously accept incoming TLS connections.
pub struct TlsServer<'a> {
    acceptor: Pin<Box<dyn Stream<Item = Result<TlsStream<TcpStream>, io::Error>> + 'a>>,
}

impl hyper::server::accept::Accept for TlsServer<'_> {
    type Conn = TlsStream<TcpStream>;
    type Error = io::Error;

    /// Poll to accept the next connection.
    fn poll_accept(
        mut self: Pin<&mut Self>,
        cx: &mut Context,
    ) -> Poll<Option<Result<Self::Conn, Self::Error>>> {
        let connection = Pin::new(&mut self.acceptor).poll_next(cx);
        match connection {
            // When a connections fails, for example due to a `CertificateUnknown` error, we want to
            // keep the server alive and waiting for new connections. The `poll_accept` method has
            // to return `Poll::Pending` in these cases, to in turn cause the `poll` method of the
            // hyper server to return `Poll::Pending`, making the server wait for the next
            // connection. The `poll_watch` method in `hyper::server::conn::SpawnAll`,
            // which calls `poll_accept` will make sure that the server is scheduled to
            // be awoken when there is a new incoming connection, by calling `wake` on
            // the `waker` in the context `cx`.
            Poll::Ready(Some(Err(e))) => {
                error!("Error when processing TLS stream: {:?}", e);
                Poll::Pending
            }
            _ => connection,
        }
    }
}

/// Struct that represents an HTTP server pseudo-Node.
pub struct HttpServerNode {
    /// Pseudo-Node name.
    node_name: String,
    /// Server address to listen client requests on.
    address: SocketAddr,
    /// TLS certificate and private key for establishing secure connections.
    tls_config: crate::tls::TlsConfig,
}

impl HttpServerNode {
    /// Creates a new [`HttpServerNode`] instance, but does not start it.
    pub fn new(
        node_name: &str,
        config: HttpServerConfiguration,
        tls_config: crate::tls::TlsConfig,
    ) -> Result<Self, ConfigurationError> {
        let address = config.address.parse()?;
        check_port(&address)?;
        Ok(Self {
            node_name: node_name.to_string(),
            address,
            tls_config,
        })
    }

    /// Make a server, with graceful shutdown, from the given [`HttpRequestHandler`].
    async fn make_server(
        &self,
        request_handler: HttpRequestHandler,
        notify_receiver: tokio::sync::oneshot::Receiver<()>,
    ) {
        // A `Service` is needed for every connection, so this
        // creates one from the `request_handler`.
        let service = make_service_fn(move |_conn| {
            let handler = request_handler.clone();
            async move {
                Ok::<_, hyper::Error>(service_fn(move |req| {
                    let handler = handler.clone();
                    async move { handler.handle(req).await }
                }))
            }
        });

        // Low-level server creation is needed, to be able to validate TLS streams.
        let mut tcp = match TcpListener::bind(&self.address).await {
            Ok(tcp) => tcp,
            Err(e) => {
                error!(
                    "{:?}: Could not create TCP listener: {:?}",
                    std::thread::current().id(),
                    e
                );
                return;
            }
        };
        let tls_server = self.build_tls_server(&mut tcp);
        let server = Server::builder(tls_server).serve(service);

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
        info!(
            "HTTP server pseudo-node on addr {:?} terminated with {:?}",
            self.address, result
        );
    }

    /// Build a server that checks incoming TCP connections for TLS handshake.
    fn build_tls_server<'a>(&'a self, tcp: &'a mut TcpListener) -> TlsServer<'a> {
        let tls_cfg = crate::tls::to_server_config(self.tls_config.clone());
        let tls_acceptor = TlsAcceptor::from(tls_cfg);

        let incoming_tls_stream = tcp
            .incoming()
            .map_err(|err| {
                io::Error::new(io::ErrorKind::Other, format!("Incoming failed: {:?}", err))
            })
            .and_then(move |stream| {
                debug!("Received incoming TLS stream: {:?}", stream);
                tls_acceptor.accept(stream).map_err(|err| {
                    error!("Client-connection error: {:?}", err);
                    io::Error::new(io::ErrorKind::Other, format!("TLS Error: {:?}", err))
                })
            })
            .boxed();

        TlsServer {
            acceptor: incoming_tls_stream,
        }
    }
}

/// Oak Node implementation for the HTTP server.
impl Node for HttpServerNode {
    fn node_type(&self) -> &'static str {
        "http-server"
    }

    fn external_facing(&self) -> bool {
        true
    }

    fn get_privilege(&self) -> NodePrivilege {
        // This node needs to have `top` privilege to be able to declassify data tagged with any
        // arbitrary user identities.
        // TODO(#1631): When we have a separate top for each sub-lattice, this should be changed to
        // the top of the `user` sub-lattice.
        NodePrivilege::top_privilege()
    }

    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        startup_handle: oak_abi::Handle,
        notify_receiver: oneshot::Receiver<()>,
    ) {
        // At start-of-day we need/expect to receive a write handle for an invocation channel
        // to use for all subsequent activity.
        info!("{}: Waiting for invocation channel", self.node_name);
        let startup_receiver = Receiver::<HttpInvocationSender>::new(ReadHandle {
            handle: startup_handle,
        });
        let invocation_channel =
            match startup_receiver
                .receive(&runtime)
                .and_then(|invocation_sender| {
                    invocation_sender
                        .sender
                        .ok_or(OakError::OakStatus(OakStatus::ErrBadHandle))
                }) {
                Ok(sender) => sender.handle.handle,
                Err(status) => {
                    error!(
                        "Failed to retrieve invocation channel write handle: {:?}",
                        status
                    );
                    return;
                }
            };
        if let Err(err) = startup_receiver.close(&runtime) {
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
    async fn handle(&self, req: Request<Body>) -> Result<Response<Body>, OakStatus> {
        // Hyper requires an error type that implements [`std::error::Error`]. [`HttpError`] does
        // not currently implement this trait. So, this wrapper is added to log and convert the
        // error.
        // TODO(#1693): Use anyhow instead of HttpError.
        self.handle_request(req).await.map_err(|err| {
            warn!("Error when handling the request: {:?}", err);
            OakStatus::ErrInternal
        })
    }

    async fn handle_request(&self, req: Request<Body>) -> Result<Response<Body>, HttpError> {
        let request = to_oak_http_request(req).await?;
        match get_oak_label(&request) {
            Ok(oak_label) => {
                info!(
                    "Handling HTTP request; request body size: {} bytes, label: {:?}",
                    request.body.len(),
                    oak_label
                );

                debug!("Injecting the request into the Oak Node");
                let response = self
                    .inject_http_request(request, oak_label)
                    .map_err(|err| {
                        HttpError::ChannelOperation(format!(
                            "Error when injecting the request into the Oak Node: {:?}",
                            err
                        ))
                    })?;

                response.try_into_hyper_response()
            }
            Err(HttpError::RequestLabel(msg)) => {
                warn!("Invalid or missing Oak label: {}", msg);
                http::response::Builder::new()
                    .status(StatusCode::BAD_REQUEST)
                    .body(Body::from("Invalid or missing Oak label."))
                    .map_err(|e| {
                        HttpError::HttpResponse(format!("Could not create response: {}", e))
                    })
            }
            Err(HttpError::IdentityVerification(msg)) => {
                warn!("Could not verify user's identity: {}", msg);
                http::response::Builder::new()
                    .status(StatusCode::BAD_REQUEST)
                    .body(Body::from("Could not verify user's identity."))
                    .map_err(|e| {
                        HttpError::HttpResponse(format!("Could not create response: {}", e))
                    })
            }
            Err(http_err) => {
                warn!("Internal server error: {:?}", http_err);
                http::response::Builder::new()
                    .status(StatusCode::INTERNAL_SERVER_ERROR)
                    .body(Body::from("Internal server error."))
                    .map_err(|e| {
                        HttpError::HttpResponse(format!("Could not create response: {}", e))
                    })
            }
        }
    }

    /// Creates a pair of channels for interaction with the Oak node, and sends the request to the
    /// Oak node. If the request is successfully handled, this function returns an
    /// [`HttpResponseReceiver`] with a handle to the channel containing the response.
    fn inject_http_request(
        &self,
        request: HttpRequest,
        request_label: Label,
    ) -> Result<HttpResponseReceiver, HttpError> {
        let user_identity = get_user_identity(&request)?;
        let user_identity_label = if user_identity.is_empty() {
            // If no identity is provided, return public-untrusted
            Label::public_untrusted()
        } else {
            confidentiality_label(public_key_identity_tag(user_identity))
        };

        // Create a pair of temporary channels to pass the HTTP request to the Oak Node, and
        // receive the response.
        let pipe = Pipe::new(&self.runtime.clone(), &request_label, &user_identity_label)?;

        // Put the HTTP request message inside the per-invocation request channel.
        pipe.insert_message(&self.runtime, request)?;

        // Send an invocation message (with attached handles) to the Oak Node.
        pipe.send_invocation(&self.runtime, self.invocation_channel)?;

        // Close all local handles except for the one that allows reading responses.
        pipe.close(&self.runtime);

        Ok(HttpResponseReceiver {
            runtime: self.runtime.clone(),
            response_reader: pipe.response_reader,
        })
    }
}

/// A pair of temporary channels to pass the HTTP request to the Oak Node and receive the response.
struct Pipe {
    request_writer: oak_abi::Handle,
    request_reader: oak_abi::Handle,
    response_writer: oak_abi::Handle,
    response_reader: oak_abi::Handle,
}

impl Pipe {
    fn new(
        runtime: &RuntimeProxy,
        request_label: &Label,
        user_identity_label: &Label,
    ) -> Result<Self, HttpError> {
        // Create a channel for passing HTTP requests to the Oak node. This channel is created with
        // the label specified by the caller. Without a `public_fully_trusted` label or a privilege
        // that allows removing integrity tags, this will fail if the label has a non-empty
        // integrity component.
        let (request_writer, request_reader) = runtime
            .channel_create("HTTP request", request_label)
            .map_err(|err| {
                HttpError::ChannelOperation(format!(
                    "could not create HTTP request channel: {:?}",
                    err
                ))
            })?;

        let (response_writer, response_reader) = runtime
            .channel_create("HTTP response", user_identity_label)
            .map_err(|err| {
                HttpError::ChannelOperation(format!(
                    "could not create HTTP response channel: {:?}",
                    err
                ))
            })?;

        Ok(Pipe {
            request_writer,
            request_reader,
            response_writer,
            response_reader,
        })
    }

    /// Inserts the incoming HTTP request in the `request channel` part of the `HttpInvocation`.
    fn insert_message(
        &self,
        runtime: &RuntimeProxy,
        request: HttpRequest,
    ) -> Result<(), HttpError> {
        // Put the HTTP request message inside the per-invocation request channel.
        let sender = crate::io::Sender::new(WriteHandle {
            handle: self.request_writer,
        });
        sender.send(request, runtime).map_err(|err| {
            HttpError::ChannelOperation(format!(
                "Couldn't write the request to the HTTP request channel: {:?}",
                err
            ))
        })
    }

    /// Sends the `HttpInvocation` with request and response channels to the Oak Node.
    fn send_invocation(
        &self,
        runtime: &RuntimeProxy,
        invocation_channel: oak_abi::Handle,
    ) -> Result<(), HttpError> {
        // Create an invocation containing request-specific channels.
        let invocation = HttpInvocation {
            receiver: Some(Receiver::new(ReadHandle {
                handle: self.request_reader,
            })),
            sender: Some(Sender::new(WriteHandle {
                handle: self.response_writer,
            })),
        };
        let invocation_sender = crate::io::Sender::new(WriteHandle {
            handle: invocation_channel,
        });
        invocation_sender
            .send(invocation, runtime)
            .map_err(|error| {
                HttpError::ChannelOperation(format!(
                    "Couldn't write the invocation message: {:?}",
                    error
                ))
            })
    }

    /// Close all local handles except for the one that allows reading responses.
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

/// HTTP requests can either provide JSON formatted labels or protobuf encoded labels. But exactly
/// one of these should be provided. This method checks that exactly one label is provided in a
/// header in the request and extracts it for use for further handling of the request.
fn get_oak_label(req: &HttpRequest) -> Result<Label, HttpError> {
    let headers = (
        req.headers.as_ref().and_then(|map| {
            map.headers
                .get(oak_abi::OAK_LABEL_HTTP_JSON_KEY)
                .map(|m| m.values.as_slice())
        }),
        req.headers.as_ref().and_then(|map| {
            map.headers
                .get(oak_abi::OAK_LABEL_HTTP_PROTOBUF_KEY)
                .map(|m| m.values.as_slice())
        }),
    );

    match headers {
        (Some([json_label]), None) => parse_json_label(json_label),
        (None, Some([protobuf_label])) => parse_protobuf_label(protobuf_label),
        _ => Err(HttpError::RequestLabel(format!(
            "Exactly one request label must be provided via an {} or an {} header.",
            oak_abi::OAK_LABEL_HTTP_JSON_KEY,
            oak_abi::OAK_LABEL_HTTP_PROTOBUF_KEY
        ))),
    }
}

/// Similar to the request label headers, signed challenge headers can either be JSON formatted or
/// protobuf encoded. At most one of these formats should be provided. This method:
///
/// 1. parses the signed challenge, if one is provided
/// 2. verifies that the signature is valid
/// 3. if the signature is valid, returns the public key in the signed challenge as the user's
/// identity.
///
/// Providing the user's identity in the HTTP request is optional, so if a challenge response is
/// not provided, an empty vector is returned.
fn get_user_identity(req: &HttpRequest) -> Result<Vec<u8>, HttpError> {
    let headers = (
        req.headers.as_ref().and_then(|map| {
            map.headers
                .get(oak_abi::OAK_SIGNED_CHALLENGE_JSON_KEY)
                .map(|m| m.values.as_slice())
        }),
        req.headers.as_ref().and_then(|map| {
            map.headers
                .get(oak_abi::OAK_SIGNED_CHALLENGE_PROTOBUF_KEY)
                .map(|m| m.values.as_slice())
        }),
    );

    match headers {
        (Some([json_signature]), None) => verify_json_challenge(json_signature),
        (None, Some([protobuf_signature])) => verify_protobuf_challenge(protobuf_signature),
        (None, None) => Ok(vec![]),
        _ => Err(HttpError::IdentityVerification(format!(
            "At most one signed-challenge must be provided via an {} or an {} header.",
            oak_abi::OAK_SIGNED_CHALLENGE_JSON_KEY,
            oak_abi::OAK_SIGNED_CHALLENGE_PROTOBUF_KEY
        ))),
    }
}

fn parse_json_label(label_str: &[u8]) -> Result<Label, HttpError> {
    let label_str = String::from_utf8(label_str.to_vec()).map_err(|err| {
        HttpError::RequestLabel(format!(
            "The label must be a valid UTF-8 JSON-formatted string: {}",
            err
        ))
    })?;
    serde_json::from_str(&label_str)
        .map_err(|err| HttpError::RequestLabel(format!("Could not parse HTTP label: {}", err)))
}

fn parse_protobuf_label(base64_protobuf_label: &[u8]) -> Result<Label, HttpError> {
    let protobuf_label = base64::decode(base64_protobuf_label).map_err(|err| {
        HttpError::RequestLabel(format!("Could not decode Base64 HTTP label: {}", err))
    })?;
    Label::decode(&protobuf_label[..])
        .map_err(|err| HttpError::RequestLabel(format!("Could not parse HTTP label: {}", err)))
}

/// Checks that the input signature (containing the signed challenge and the corresponding public
/// key) is valid. If the signature is valid, this function returns the public key, otherwise
/// returns an [`HttpError`].
fn verify_json_challenge(signature: &[u8]) -> Result<Vec<u8>, HttpError> {
    let signature = parse_json_signed_challenge(signature.to_vec()).map_err(|err| {
        HttpError::IdentityVerification(format!(
            "Could not parse json formatted signed challenge: {:?}",
            err
        ))
    })?;
    verify_signed_challenge(signature)
}

/// Tries to parse the signed challenge retrieved from the HTTP request into an instance of
/// [`SignedChallenge`]. If not successful, returns an [`HttpError`].
fn parse_json_signed_challenge(bytes: Vec<u8>) -> Result<SignedChallenge, HttpError> {
    let signature_str = String::from_utf8(bytes).map_err(|err| {
        HttpError::IdentityVerification(format!("Could not parse signed challenge: {:?}", err))
    })?;
    serde_json::from_str(&signature_str).map_err(|err| {
        HttpError::IdentityVerification(format!("Malformed signed challenge: {:?}", err))
    })
}

/// Checks that the input signature (containing the signed challenge and the corresponding public
/// key) is valid. If the signature is valid, this function returns the public key, otherwise it
/// returns an [`HttpError`].
fn verify_protobuf_challenge(base64_signature: &[u8]) -> Result<Vec<u8>, HttpError> {
    let signature_bytes = base64::decode(base64_signature).map_err(|err| {
        HttpError::IdentityVerification(format!(
            "Could not decode Base64 signed challenge: {}",
            err
        ))
    })?;
    let signature = SignedChallenge::decode(&signature_bytes[..]).map_err(|err| {
        HttpError::IdentityVerification(format!(
            "Could not parse protobuf encoded signed challenge: {}",
            err
        ))
    })?;
    verify_signed_challenge(signature)
}

/// Verifies the signed challenge retrieved from the HTTP request, and returns the public key if the
/// signature is valid.
fn verify_signed_challenge(
    signature: oak_abi::proto::oak::identity::SignedChallenge,
) -> Result<Vec<u8>, HttpError> {
    let hash = oak_sign::get_sha256(oak_abi::OAK_CHALLENGE.as_bytes());

    let sig_bundle = oak_sign::SignatureBundle {
        public_key: signature.public_key.clone(),
        signed_hash: signature.signed_hash,
        hash,
    };

    match sig_bundle.verify() {
        Ok(()) => Ok(signature.public_key),
        Err(err) => Err(HttpError::IdentityVerification(format!(
            "Could not verify the signature: {}.",
            err
        ))),
    }
}

struct HttpResponseReceiver {
    runtime: RuntimeProxy,
    response_reader: oak_abi::Handle,
}

impl HttpResponseReceiver {
    fn read_response(&self) -> Result<HttpResponse, OakError> {
        let response_receiver = crate::io::Receiver::<HttpResponse>::new(ReadHandle {
            handle: self.response_reader,
        });
        response_receiver.receive(&self.runtime)
    }

    fn try_into_hyper_response(&self) -> Result<Response<Body>, HttpError> {
        info!(
            "Generating response for runtime {} and reader {:?}.",
            self.runtime.node_id.0, self.response_reader
        );
        match self.read_response() {
            Ok(http_response) => to_hyper_response(http_response),
            Err(status) => {
                warn!("Could not read response: {}", status);
                http::response::Builder::new()
                    .status(StatusCode::INTERNAL_SERVER_ERROR)
                    .body(Body::empty())
                    .map_err(|err| {
                        HttpError::HttpResponse(format!("Could not create response: {}", err))
                    })
            }
        }
    }
}

/// Create an instance of Oak HttpRequest from the given hyper Request.
async fn to_oak_http_request(req: Request<Body>) -> Result<HttpRequest, HttpError> {
    let uri = req.uri().to_string();
    let method = req.method().as_str().to_string();
    let headers = Some(HeaderMap::from(req.headers().to_owned()));
    let body = hyper::body::to_bytes(req.into_body())
        .await
        .map_err(|err| {
            HttpError::HttpRequest(format!(
                "Error when reading request body from the connection: {}",
                err
            ))
        })?
        .to_vec();

    Ok(HttpRequest {
        uri,
        method,
        body,
        headers,
    })
}

/// Convert an instance of Oak HttpResponse to hyper Response.
fn to_hyper_response(http_response: HttpResponse) -> Result<Response<Body>, HttpError> {
    let mut builder = http::response::Builder::new();
    if let Some(headers) = http_response.headers {
        let headers = headers.into_iter();
        for (header_name, header_value) in headers {
            builder = builder.header(header_name, header_value);
        }
    }

    builder
        .status(http_response.status as u16)
        .body(Body::from(http_response.body))
        .map_err(|err| HttpError::HttpResponse(format!("Could not build response: {}", err)))
}
