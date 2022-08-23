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
use http::{Method, Uri};
use hyper::{Body, Client, Request, Response, StatusCode};
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

        match send_to_backend(request).await {
            Err(error) => Err(anyhow!(
                "Couldn't receive response from the backend: {:?}",
                error
            )),
            Ok(response) => Ok(hyper_to_trusted_shuffler_response(response).await),
        }
    }
}

async fn send_to_backend(request: Request<Body>) -> anyhow::Result<Response<Body>> {
    let client: Client<AlpnConnector> = Client::builder()
        .http2_only(true)
        .build(AlpnConnector::new());

    let response =
        anyhow::Context::context(client.request(request).await, "Couldn't send request")?;
    if response.status() != http::StatusCode::OK {
        return Err(anyhow!("Non-OK status: {:?}", response.status()));
    }

    Ok(response)
}

// We keep the body and the URI from the `hyper::Request`. We convert the body to `Vec`, so it has
// to be read fully.
async fn hyper_to_trusted_shuffler_request(hyper_request: Request<Body>) -> TrustedShufflerRequest {
    let (parts, body) = hyper_request.into_parts();
    let body = hyper::body::to_bytes(body)
        .await
        .expect("Couldn't read request body");
    log::info!("Body {:?}", body);
    TrustedShufflerRequest {
        body: body.to_vec(),
        uri: parts.uri.clone(),
    }
}

// Apart from setting the body and the URI, for our test backend setting to HTTP/2 and POST
// seems sufficient.
fn trusted_shuffler_to_hyper_request(
    trusted_shuffler_request: TrustedShufflerRequest,
) -> Request<Body> {
    let body = Body::from(trusted_shuffler_request.body);

    Request::builder()
        .uri(trusted_shuffler_request.uri)
        .method(Method::POST)
        .header("content-type", "application/grpc")
        .version(http::Version::HTTP_2)
        .body(body)
        .expect("Failed to convert Trusted to Hyper Request")
}

// We generate a default `hyper::Response`. We convert the body to `Vec`, so it has to be
// read fully.
async fn trusted_shuffler_to_hyper_response(
    trusted_shuffler_response: TrustedShufflerResponse,
) -> Response<Body> {
    log::info!("Response: {:?}", trusted_shuffler_response);
    let body = Body::from(trusted_shuffler_response.body);

    let streamed_body = hyper::body::to_bytes(body)
        .await
        .expect("Couldn't read response body.");

    Response::builder()
        .header("content-type", "application/grpc")
        .body(Body::from(streamed_body))
        .expect("Failed to convert Trusted to Hyper Response.")
}

// We keep only the body from the `hyper::Response`. We convert the body to `Vec`, so it has to be
// read fully.
async fn hyper_to_trusted_shuffler_response(
    hyper_response: Response<Body>,
) -> TrustedShufflerResponse {
    log::info!("Response from backend: {:?}", hyper_response);
    let body = hyper::body::to_bytes(hyper_response.into_body())
        .await
        .expect("Couldn't read request body");
    TrustedShufflerResponse {
        body: body.to_vec(),
    }
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
