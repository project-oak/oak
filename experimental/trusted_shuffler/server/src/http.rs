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
use hyper::{Body, Method, Request, Response, StatusCode};
use log::{error, info};
use std::{
    future::Future,
    pin::Pin,
    sync::Arc,
    task::{Context, Poll},
};
use trusted_shuffler::{RequestHandler, TrustedShuffler};
use trusted_shuffler_common::send_request;

struct HttpRequestHandler {
    backend_url: String,
}

#[async_trait]
impl RequestHandler for HttpRequestHandler {
    async fn handle(&self, request: Vec<u8>) -> anyhow::Result<Vec<u8>> {
        let response = send_request(&self.backend_url, Method::POST, &request).await;
        response.map_or_else(
            |error| {
                Err(anyhow!(
                    "Couldn't receive response from the backend: {:?}",
                    error
                ))
            },
            |response| {
                info!("Received response from the backend: {:?}", response);
                Ok(response)
            },
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
        let trusted_shuffler = self.trusted_shuffler.clone();
        let response = async move {
            match (request.method(), request.uri().path()) {
                (&Method::POST, "/request") => {
                    let body = hyper::body::to_bytes(request.into_body())
                        .await
                        .expect("Couldn't read request body");
                    info!("Received request: {:?}", body);

                    match trusted_shuffler.invoke(body.to_vec()).await {
                        Ok(response) => {
                            info!("Received response: {:?}", response);
                            Ok(Response::new(Body::from(response)))
                        }
                        Err(error) => {
                            error!("Couldn't receive response: {:?}", error);
                            let mut internal_error = Response::default();
                            *internal_error.status_mut() = StatusCode::INTERNAL_SERVER_ERROR;
                            Ok(internal_error)
                        }
                    }
                }
                _ => {
                    let mut not_found = Response::default();
                    *not_found.status_mut() = StatusCode::NOT_FOUND;
                    Ok(not_found)
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
    pub fn new(k: usize, backend_url: &str) -> Self {
        let trusted_shuffler = Arc::new(TrustedShuffler::new(
            k,
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
