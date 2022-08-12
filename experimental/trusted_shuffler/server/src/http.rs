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
use hyper::{Body, Request, Response, StatusCode};
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
use trusted_shuffler_common::send_with_request;

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
        let new_uri = match  format!("{}{}", self.backend_url, path).parse::<Uri>() {
            Ok(new_uri) => new_uri,
            Err(error) => return Err(anyhow!("Couldn't parse URI for backend: {:?}", error))
        };
        let uri = request.uri_mut();
        *uri = new_uri;

        log::info!("New request to the backend: {:?}", request);

        match send_with_request(request).await {
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
        .version(http::Version::HTTP_2)
        .body(body)
        .expect("Failed to convert Trusted to Hyper Request")
}

// We generate a default `hyper::Response` and set only the body.
fn trusted_shuffler_to_hyper_response(
    trusted_shuffler_request: TrustedShufflerResponse,
) -> Response<Body> {
    let body = Body::from(trusted_shuffler_request.body);
    Response::new(body)
}

// We keep only the body from the `hyper::Response`. We convert the body to `Vec`, so it has to be
// read fully.
async fn hyper_to_trusted_shuffler_response(
    hyper_response: Response<Body>,
) -> TrustedShufflerResponse {
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
                    Ok(trusted_shuffler_to_hyper_response(response))
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
