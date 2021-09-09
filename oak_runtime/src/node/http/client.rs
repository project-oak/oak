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

//! HTTP client pseudo-Node that allows sending HTTP requests to a specific external service.

use crate::{
    io::{Receiver, ReceiverExt},
    node::{invocation::InvocationExt, ConfigurationError, Node},
    proto::oak::invocation::HttpInvocation as Invocation,
    NodePrivilege, RuntimeProxy,
};
use http::{uri::Scheme, Uri};
use hyper::body::to_bytes;
use log::{debug, error, info, warn};
use maplit::hashset;
use oak_abi::{proto::oak::application::HttpClientConfiguration, Handle, OakStatus};
use oak_io::{handle::ReadHandle, OakError};
use oak_services::proto::oak::encap::{HeaderMap, HttpResponse};
use std::io;
use tokio::sync::oneshot;

type HyperClient =
    hyper::client::Client<hyper_rustls::HttpsConnector<hyper::client::HttpConnector>, hyper::Body>;

/// Struct that represents an HTTP client pseudo-Node.
pub struct HttpClientNode {
    /// Pseudo-Node name.
    node_name: String,
    /// HTTP client to allow re-use of connection across multiple method invocations. It can be
    /// used to send either HTTP or HTTPS requests.
    http_client: HyperClient,
    /// The authority supported by this client. It must match the client's label. If the
    /// authority is non-empty, only HTTPS requests with the same authority component in their
    /// URIs can be handled. If the authority is empty, the client must be public and it may
    /// handle arbitrary requests to any HTTP or HTTPS services.
    authority: String,
}

/// Oak Node implementation for the HTTP client pseudo-Node.
impl Node for HttpClientNode {
    fn node_type(&self) -> &'static str {
        "HTTP-client"
    }

    fn run(
        mut self: Box<Self>,
        runtime: RuntimeProxy,
        handle: Handle,
        notify_receiver: oneshot::Receiver<()>,
    ) {
        // Create an Async runtime for executing futures.
        // https://docs.rs/tokio/
        // TODO(#1280): Use a single shared tokio runtime, instead of creating a new one here.
        let async_runtime = create_async_runtime();

        // Listen to incoming HTTP invocations.
        info!(
            "{}: Starting HTTP client pseudo-Node thread",
            self.node_name
        );
        async_runtime.block_on(futures_util::future::select(
            Box::pin(self.handle_loop(runtime, handle)),
            notify_receiver,
        ));
        info!("{}: Exiting HTTP client pseudo-Node thread", self.node_name);
    }
}

pub(crate) fn get_privilege(authority: &str) -> NodePrivilege {
    if authority.is_empty() {
        NodePrivilege::default()
    } else {
        NodePrivilege::new(
            hashset! { oak_abi::label::tls_endpoint_tag(authority) },
            hashset! { oak_abi::label::tls_endpoint_tag(authority) },
        )
    }
}

#[derive(Debug)]
enum ProcessingError {
    InvalidUri,
    ReadFailed(OakError),
    PermissionDenied,
    UnsupportedScheme,
    BodyConversionError(http::Error),
    InterruptedWaitForResponse(hyper::Error),
    ResponseHandlingError,
}

impl HttpClientNode {
    /// Creates a new `HttpClientNode` that can handle HTTP or HTTPS requests. If the `config`
    /// specifies a non-empty authority, only HTTPS requests with the same authority component in
    /// their URIs can be handled. The authority must also match the label with which this node
    /// is being created. If the authority provided in the config is empty, then the node must
    /// be labelled public. In this case, the node can handle any arbitrary requests to any HTTP
    /// or HTTPS services.
    pub fn new(
        node_name: &str,
        config: HttpClientConfiguration,
        root_ca: crate::tls::Certificate,
    ) -> Result<Self, ConfigurationError> {
        let http_client = create_client(root_ca);
        Ok(HttpClientNode {
            node_name: node_name.to_string(),
            http_client,
            authority: config.authority,
        })
    }

    /// Main loop that handles HTTP/HTTPS invocations, sends the requests to an external HTTP or
    /// HTTPS service and writes responses back to the invocation channel.
    async fn handle_loop(&mut self, runtime: RuntimeProxy, handle: Handle) -> Result<(), OakError> {
        // Create a [`Receiver`] to receive the HTTP/HTTPS request.
        let receiver = Receiver::<Invocation>::new(ReadHandle { handle });
        loop {
            debug!("Waiting for HTTP invocation");
            // Read an HTTP invocation from the [`Receiver`].
            let invocation = receiver.receive(&runtime).map_err(|error| {
                match error {
                    OakError::OakStatus(OakStatus::ErrTerminated) => {
                        debug!("HTTP client node is terminating.")
                    }
                    OakError::OakStatus(OakStatus::ErrChannelClosed) => {
                        info!("HTTP invocation channel closed")
                    }
                    _ => error!("Couldn't receive the invocation: {:?}", error),
                }
                error
            })?;

            // Process the request and send an INTERNAL_SERVER_ERROR (500) response to the caller if
            // there is an error.
            if let Err(err) = self.process_invocation(&runtime, &invocation).await {
                warn!("{:?}", err);
                invocation.send_error(
                    http::StatusCode::INTERNAL_SERVER_ERROR,
                    &format!("{:?}", err),
                    &runtime,
                );
            }
            info!("HTTP client: Invocation processing finished");
            invocation.close(&runtime);
        }
    }

    /// Process an HTTP invocation for an external HTTP/HTTPS service.
    async fn process_invocation(
        &mut self,
        runtime: &RuntimeProxy,
        invocation: &Invocation,
    ) -> Result<(), ProcessingError> {
        // TODO(#1717): Update HTTP client metrics

        // Receive a request from the invocation channel.
        let request = invocation
            .receive_request(runtime)
            .map_err(ProcessingError::ReadFailed)?;
        debug!("Incoming HTTP request: {:?}", request);

        let uri = request
            .uri
            .parse::<Uri>()
            .map_err(|_err| ProcessingError::InvalidUri)?;

        // Check that the client is allowed to handle the incoming request.
        self.validate_uri(&uri)?;

        let mut hyper_request_builder = hyper::Request::builder()
            .method(request.method.as_str())
            .uri(uri);

        if let Some(headers) = request.headers {
            for (header_name, header_value) in headers.into_iter() {
                hyper_request_builder = hyper_request_builder.header(header_name, header_value);
            }
        }
        let hyper_request = hyper_request_builder
            .body(hyper::Body::from(request.body))
            .map_err(ProcessingError::BodyConversionError)?;

        // Forward the request to the external HTTP service and wait for the response.
        let resp = self
            .http_client
            .request(hyper_request)
            .await
            .map_err(ProcessingError::InterruptedWaitForResponse)?;

        info!("HTTP client: Handling the response...");
        let mut response_handler = ResponseHandler::new(runtime.clone(), resp, invocation);
        response_handler.handle().await
    }

    /// Check that the client is permitted to handle requests to the given URI.
    fn validate_uri(&self, uri: &Uri) -> Result<(), ProcessingError> {
        // If this node has a non-empty authority, check that:
        // - the request uses the `HTTPS` scheme, and
        // - the `authority` in the request's URI is present, and matches the authority of the node.
        if !self.authority.is_empty() {
            uri.scheme()
                .filter(|scheme| **scheme == Scheme::HTTPS)
                .ok_or(ProcessingError::UnsupportedScheme)?;
            uri.authority()
                .filter(|auth| *auth.to_owned() == self.authority)
                .ok_or(ProcessingError::PermissionDenied)?;
        }
        // Otherwise (for empty authority), return OK, as the node is public and can handle any
        // arbitrary requests.
        Ok(())
    }
}

struct ResponseHandler<'a> {
    runtime: RuntimeProxy,
    response: http::Response<hyper::Body>,
    invocation: &'a Invocation,
}

impl<'a> ResponseHandler<'a> {
    fn new(
        runtime: RuntimeProxy,
        response: http::Response<hyper::Body>,
        invocation: &'a Invocation,
    ) -> Self {
        ResponseHandler {
            runtime,
            response,
            invocation,
        }
    }

    async fn handle(&mut self) -> Result<(), ProcessingError> {
        // TODO(#1717): Update HTTP client metrics

        let headers = Some(HeaderMap::from(self.response.headers().to_owned()));
        let status = self.response.status().as_u16() as i32;
        let body = self.response.body_mut();
        let body = to_bytes(body)
            .await
            .map(|bytes| bytes.to_vec())
            .map_err(|err| {
                error!(
                    "Error when converting the response body into bytes: {:?}",
                    err
                );
                ProcessingError::ResponseHandlingError
            })?;

        let response = HttpResponse {
            body,
            status,
            headers,
        };

        // Send the response back to the invocation channel.
        debug!("Sending the HTTP response: {:?}", self.response);
        self.invocation
            .send_response(response, &self.runtime)
            .map_err(|error| {
                error!(
                    "Couldn't send the HTTP response to the invocation: {:?}",
                    error
                );
                ProcessingError::ResponseHandlingError
            })?;

        Ok(())
    }
}

fn create_async_runtime() -> tokio::runtime::Runtime {
    // Use simple scheduler that runs all tasks on the current-thread.
    // https://docs.rs/tokio/1.5.0/tokio/runtime/index.html#current-thread-scheduler
    tokio::runtime::Builder::new_current_thread()
        // Enables the I/O driver.
        // Necessary for using net, process, signal, and I/O types on the Tokio runtime.
        .enable_io()
        // Enables the time driver.
        // Necessary for creating a Tokio Runtime.
        .enable_time()
        .build()
        .expect("Couldn't create Async runtime")
}

/// Creates a client that allows `Uri`s with either the `HTTP` or the `HTTPS` scheme.
fn create_client(root_ca: crate::tls::Certificate) -> HyperClient {
    // Build an HTTP connector which supports HTTPS too.
    let mut http = hyper::client::HttpConnector::new();
    // Allow the client to handle both HTTP and HTTPS requests.
    http.enforce_http(false);

    let ca_file = io::Cursor::new(root_ca);
    let mut ca_reader = io::BufReader::new(ca_file);

    // Build a TLS client, using the custom CA store for lookups.
    let mut tls = rustls::ClientConfig::new();
    tls.root_store
        .add_pem_file(&mut ca_reader)
        .expect("failed to load custom CA store");
    // Join the above part into an HTTPS connector.
    let https = hyper_rustls::HttpsConnector::from((http, tls));
    hyper::client::Client::builder().build(https)
}
