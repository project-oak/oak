//
// Copyright 2022 The Project Oak Authors
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

use anyhow::{anyhow, Context};
use async_trait::async_trait;
use http::{header, Method, Uri};
use hyper::{body::HttpBody, Body, Client, Request, Response, StatusCode};
use hyper_alpn::AlpnConnector;
use std::{future::Future, pin::Pin, sync::Arc, task::Poll, time::Instant};
use tokio::time::Duration;
use trusted_shuffler::{
    PlainRequest, PlainResponse, RequestHandler, SecretRequest, SecretResponse, TrustedShuffler,
};

struct HttpRequestHandler {
    backend_url: String,
}

#[async_trait]
impl RequestHandler for HttpRequestHandler {
    async fn handle(&self, request: PlainRequest) -> anyhow::Result<PlainResponse> {
        let mut request = trusted_shuffler_to_hyper_request(request)?;

        // We want to keep the path of the orginal request from the client.
        //
        // The following does not work, because &self would need 'static life time.
        // let parts = request.uri().into_parts();
        // parts.authority = Some(Authority::from_static(&self.backend_url));
        // let new_uri = Uri::from_parts(parts).expect("Failed to create new URI");
        let path = request.uri().path();
        // And extend the URL to the backend.
        let new_uri = format!("{}{}", self.backend_url, path)
            .parse::<Uri>()
            .map_err(|error| anyhow!("Couldn't parse URI for backend: {:?}", error))?;
        let uri = request.uri_mut();
        *uri = new_uri;

        log::info!("New request to the backend: {:?}", request);

        // If the backend_url is a https connection, we need to use the AlpnConnector for the
        // client connecting to the backend.
        let scheme = request
            .uri()
            .scheme()
            .context("Could not get scheme from backend_url.")?;

        let response = if scheme == &http::uri::Scheme::HTTPS {
            Client::builder()
                .http2_only(true)
                .build(AlpnConnector::new())
                .request(request)
        } else {
            Client::builder()
                .http2_only(true)
                .build_http()
                .request(request)
        };

        match response.await {
            Err(error) => Err(anyhow!(
                "Couldn't receive response from the backend: {:?}",
                error
            )),
            Ok(response) => Ok(hyper_to_trusted_shuffler_response(response).await?),
        }
    }
}

// We keep the body and the URI from the `hyper::Request`. We convert the body to `Vec`, so it has
// to be read fully.
async fn hyper_to_trusted_shuffler_request(
    hyper_request: Request<Body>,
) -> anyhow::Result<SecretRequest> {
    let (parts, body) = hyper_request.into_parts();
    let body = hyper::body::to_bytes(body)
        .await
        .context("Couldn't read request body")?;
    log::debug!("Body {:?}", body);

    let uri = parts.uri.clone();

    // Keep the minimal headers the backend requires to handle the request.
    let minimal_keys = vec![
        header::CONTENT_TYPE, // for gRPC requests
        header::HeaderName::from_static(
            "grpc-accept-encoding", // for gRPC requests
        ),
        header::TE, // for gRPC requests
        header::CONTENT_LENGTH,
    ];
    let minimal_headers = copy_selected_keys(parts.headers, minimal_keys);

    let trusted_shuffler_request = SecretRequest {
        body: body.to_vec(),
        headers: minimal_headers,
        uri,
    };

    Ok(trusted_shuffler_request)
}

// Apart from setting the body and the URI, for our test backend setting to HTTP/2 and POST
// seems sufficient.
fn trusted_shuffler_to_hyper_request(
    trusted_shuffler_request: PlainRequest,
) -> anyhow::Result<Request<Body>> {
    let body = Body::from(trusted_shuffler_request.body);

    let mut hyper_request = Request::builder()
        .uri(trusted_shuffler_request.uri)
        .method(Method::POST)
        .version(http::Version::HTTP_2)
        .body(body)
        .context("Failed to convert Trusted to Hyper Request")?;

    let headers = hyper_request.headers_mut();

    for (k, v) in trusted_shuffler_request.headers.iter() {
        headers.insert(k, v.clone());
    }

    Ok(hyper_request)
}

// We generate a default `hyper::Response`.
async fn trusted_shuffler_to_hyper_response(
    trusted_shuffler_response: SecretResponse,
) -> anyhow::Result<Response<Body>> {
    // We build a body from the data and the trailers from the TrustedShuffler Response.
    let (mut sender, body) = hyper::Body::channel();
    sender
        .send_data(trusted_shuffler_response.data)
        .await
        .context("Could not build body from data.")?;
    sender
        .send_trailers(trusted_shuffler_response.trailers)
        .await
        .context("Could not build body from trailers")?;

    let mut hyper_response = Response::builder()
        .version(http::Version::HTTP_2)
        .body(body)
        .context("Failed to convert Trusted to Hyper Response.")?;

    let headers = hyper_response.headers_mut();

    for (k, v) in trusted_shuffler_response.headers.iter() {
        headers.insert(k, v.clone());
    }

    Ok(hyper_response)
}

// We keep only the body, i.e., data and trailers, from the `hyper::Response`.
async fn hyper_to_trusted_shuffler_response(
    hyper_response: Response<Body>,
) -> anyhow::Result<PlainResponse> {
    log::info!("Response from backend: {:?}", hyper_response);
    let (parts, mut body) = hyper_response.into_parts();

    let minimal_keys = vec![
        header::CONTENT_TYPE,
        header::HeaderName::from_static("grpc-message"),
        header::HeaderName::from_static("grpc-status"),
    ];
    let minimal_headers = copy_selected_keys(parts.headers, minimal_keys);

    let data = hyper::body::to_bytes(&mut body)
        .await
        .context("Could not read data.")?;

    let trailers = body
        .trailers()
        .await
        .context("Could not read trailers.")?
        .unwrap_or_default();

    let trusted_shuffler_response = PlainResponse {
        headers: minimal_headers,
        data,
        trailers,
    };

    Ok(trusted_shuffler_response)
}

pub struct Service {
    trusted_shuffler: Arc<TrustedShuffler>,
}

impl hyper::service::Service<Request<Body>> for Service {
    type Response = Response<Body>;
    type Error = anyhow::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, _: &mut std::task::Context) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, request: Request<Body>) -> Self::Future {
        log::info!("Received Request: {:?}", request);
        let trusted_shuffler = self.trusted_shuffler.clone();
        let response = async move {
            // gRPC call: (&Method::POST, "/trusted_shuffler.echo.Echo/Echo")
            // HTTP call: (&Method::POST, "/request")
            let request_start = Instant::now();
            match trusted_shuffler
                .invoke(hyper_to_trusted_shuffler_request(request).await?)
                .await
            {
                Ok(response) => {
                    log::info!(
                        "Server Response: {:?} at {:?}",
                        response,
                        request_start.elapsed()
                    );
                    let response = trusted_shuffler_to_hyper_response(response).await;
                    response
                }
                Err(error) => {
                    log::error!("Couldn't receive response: {:?}", error);
                    let mut internal_error = Response::default();
                    *internal_error.status_mut() = StatusCode::INTERNAL_SERVER_ERROR;
                    Ok(internal_error)
                }
            }
        };

        Box::pin(response)
    }
}

pub struct ServiceBuilder {
    trusted_shuffler: Arc<TrustedShuffler>,
}

impl ServiceBuilder {
    pub fn new(k: usize, timeout: Option<Duration>, backend_url: &str) -> Self {
        let trusted_shuffler = Arc::new(TrustedShuffler::new(
            k,
            timeout,
            Arc::new(HttpRequestHandler {
                backend_url: backend_url.to_string(),
            }),
        ));
        Self { trusted_shuffler }
    }
}

impl<T> hyper::service::Service<T> for ServiceBuilder {
    type Response = Service;
    type Error = hyper::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, _: &mut std::task::Context) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, _: T) -> Self::Future {
        let trusted_shuffler = self.trusted_shuffler.clone();
        let future = async move { Ok(Service { trusted_shuffler }) };
        Box::pin(future)
    }
}

// Helper function copying selected headers from a given header map to a new header map.
fn copy_selected_keys(
    header_map: hyper::HeaderMap,
    keys_to_copy: Vec<hyper::header::HeaderName>,
) -> hyper::HeaderMap {
    let mut header_map_copy = hyper::HeaderMap::new();

    for key in keys_to_copy {
        if let Some(value) = header_map.get(&key) {
            header_map_copy.insert(key, value.clone());
        }
    }

    header_map_copy
}
