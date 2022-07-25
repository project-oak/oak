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
use http::Uri;
use hyper::{Body, Request, Response, StatusCode};
use std::{
    future::Future,
    pin::Pin,
    sync::Arc,
    task::{Context, Poll},
    time::Instant,
};
use tokio::time::Duration;
use trusted_shuffler::{RequestHandler, TrustedShuffler};
use trusted_shuffler_common::send_with_request;

struct HttpRequestHandler {
    backend_url: String,
}

#[async_trait]
impl RequestHandler for HttpRequestHandler {
    async fn handle(&self, mut request: Request<Body>) -> anyhow::Result<Response<Body>> {
        // We want to keep the path of the orginal request from the client.
        let path = request.uri().path();
        // And extend the URL to the backend.
        let new_uri = format!("{}{}", self.backend_url, path)
            .parse::<Uri>()
            .expect("Couldn't parse URI for backend.");
        let uri = request.uri_mut();
        *uri = new_uri;
        log::info!("New request to the backend: {:?}\n", request);

        let response = send_with_request(request).await;
        response.map_or_else(
            |error| {
                Err(anyhow!(
                    "Couldn't receive response from the backend: {:?}",
                    error
                ))
            },
            Ok,
        )
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
            // TODO(mschett): Check if http still works.
            // gRPC call: (&Method::POST, "/experimental.trusted_shuffler.echo.Echo/Echo")
            // http call: (&Method::POST, "/request")
            let request_start = Instant::now();
            match trusted_shuffler.invoke(request).await {
                Ok(response) => {
                    let _response_time = request_start.elapsed();
                    log::info!("Server Response: {:?}", response);
                    Ok(Response::new(response.into_body()))
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
