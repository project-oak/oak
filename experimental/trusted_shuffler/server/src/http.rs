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

use anyhow::anyhow;
use async_trait::async_trait;
use http::{header, Method, Uri};
use hyper::{body::HttpBody, Body, Client, Request, Response, StatusCode};
use hyper_alpn::AlpnConnector;
use std::{
    future::Future,
    pin::Pin,
    sync::Arc,
    task::{Context, Poll},
    time::Instant,
};
use tokio::time::Duration;
use trusted_shuffler::{
    RequestHandler, TrustedShuffler, TrustedShufflerRequest, TrustedShufflerResponse,
};

struct HttpRequestHandler {
    backend_url: String,
}

#[async_trait]
impl RequestHandler for HttpRequestHandler {
    async fn handle(
        &self,
        request: TrustedShufflerRequest,
    ) -> anyhow::Result<TrustedShufflerResponse> {
        let mut request = trusted_shuffler_to_hyper_request(request);

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
        let is_https_url: bool = request
            .uri()
            .scheme()
            .expect("Could not get scheme from backend_url.")
            == &http::uri::Scheme::HTTPS;

        let response = if is_https_url {
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
            Ok(response) => Ok(hyper_to_trusted_shuffler_response(response).await),
        }
    }
}

// We keep the body and the URI from the `hyper::Request`. We convert the body to `Vec`, so it has
// to be read fully.
async fn hyper_to_trusted_shuffler_request(hyper_request: Request<Body>) -> TrustedShufflerRequest {
    let (parts, body) = hyper_request.into_parts();
    let body = hyper::body::to_bytes(body)
        .await
        .expect("Couldn't read request body");
    log::info!("Body {:?}", body);

    let hyper_headers = parts.headers;

    // Keep the minimal headers the backend requires to handle the request.
    let mut minimal_headers = hyper::HeaderMap::new();

    let minimal_keys = [
        header::CONTENT_TYPE, // for gRPC requests
        header::HeaderName::from_static(
            "grpc-accept-encoding", // for gRPC requests
        ),
        header::TE, // for gRPC requests
        header::CONTENT_LENGTH,
    ];

    for key in minimal_keys {
        if let Some(value) = hyper_headers.get(&key) {
            minimal_headers.insert(key, value.clone());
        }
    }

    TrustedShufflerRequest {
        body: body.to_vec(),
        headers: minimal_headers,
        uri: parts.uri.clone(),
    }
}

// Apart from setting the body and the URI, for our test backend setting to HTTP/2 and POST
// seems sufficient.
fn trusted_shuffler_to_hyper_request(
    trusted_shuffler_request: TrustedShufflerRequest,
) -> Request<Body> {
    let body = Body::from(trusted_shuffler_request.body);

    let mut request = Request::builder()
        .uri(trusted_shuffler_request.uri)
        .method(Method::POST)
        .version(http::Version::HTTP_2)
        .body(body)
        .expect("Failed to convert Trusted to Hyper Request");

    let headers = request.headers_mut();

    for (k, v) in trusted_shuffler_request.headers.iter() {
        headers.insert(k, v.clone());
    }

    request
}

// We generate a default `hyper::Response`.
async fn trusted_shuffler_to_hyper_response(
    trusted_shuffler_response: TrustedShufflerResponse,
) -> Response<Body> {
    // We build a body from the data and the trailers from the TrustedShuffler Response.
    let (mut sender, body) = hyper::Body::channel();
    sender
        .send_data(trusted_shuffler_response.data)
        .await
        .expect("Could not build body from data.");
    sender
        .send_trailers(trusted_shuffler_response.trailers)
        .await
        .expect("Cound not build body from trailers");

    Response::builder()
        .header("content-type", "application/grpc")
        .version(http::Version::HTTP_2)
        .body(body)
        .expect("Failed to convert Trusted to Hyper Response.")
}

// We keep only the body, i.e., data and trailers, from the `hyper::Response`.
async fn hyper_to_trusted_shuffler_response(
    hyper_response: Response<Body>,
) -> TrustedShufflerResponse {
    log::info!("Response from backend: {:?}", hyper_response);
    let mut body = hyper_response.into_body();

    let data = hyper::body::to_bytes(&mut body)
        .await
        .expect("Could not read data.");

    let trailers = body
        .trailers()
        .await
        .expect("Could not read trailers.")
        .unwrap_or(http::HeaderMap::new());

    TrustedShufflerResponse { data, trailers }
}

pub struct Service {
    trusted_shuffler: Arc<TrustedShuffler>,
}

impl hyper::service::Service<Request<Body>> for Service {
    type Response = Response<Body>;
    type Error = hyper::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, _: &mut Context) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, request: Request<Body>) -> Self::Future {
        log::info!("Received Request: {:?}", request);
        let trusted_shuffler = self.trusted_shuffler.clone();
        let response = async move {
            // gRPC call: (&Method::POST, "/experimental.trusted_shuffler.echo.Echo/Echo")
            // HTTP call: (&Method::POST, "/request")
            let request_start = Instant::now();
            match trusted_shuffler
                .invoke(hyper_to_trusted_shuffler_request(request).await)
                .await
            {
                Ok(response) => {
                    log::info!(
                        "Server Response: {:?} at {:?}",
                        response,
                        request_start.elapsed()
                    );
                    let response = trusted_shuffler_to_hyper_response(response).await;
                    Ok(response)
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

    fn poll_ready(&mut self, _: &mut Context) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, _: T) -> Self::Future {
        let trusted_shuffler = self.trusted_shuffler.clone();
        let future = async move { Ok(Service { trusted_shuffler }) };
        Box::pin(future)
    }
}
