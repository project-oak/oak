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

use hyper::{Body, Method, Request, Response, StatusCode};
use log::{error, info};
use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};
use trusted_shuffler_common::send_request;

pub struct Service {
    backend_url: String,
}

impl hyper::service::Service<Request<Body>> for Service {
    type Response = Response<Body>;
    type Error = hyper::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, _: &mut Context) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, request: Request<Body>) -> Self::Future {
        let backend_url = self.backend_url.clone();
        let response = async move {
            match (request.method(), request.uri().path()) {
                (&Method::POST, "/request") => {
                    let body = hyper::body::to_bytes(request.into_body())
                        .await
                        .expect("Couldn't read request body");
                    info!("Received request: {:?}", body);

                    // TODO(#2614): Use Trusted Shuffler logic.
                    let response = send_request(&backend_url, Method::POST, &body).await;
                    response.map_or_else(
                        |error| {
                            error!("Couldn't receive response: {:?}", error);
                            let mut internal_error = Response::default();
                            *internal_error.status_mut() = StatusCode::INTERNAL_SERVER_ERROR;
                            Ok(internal_error)
                        },
                        |response| {
                            info!("Received response: {:?}", response);
                            Ok(Response::new(Body::from(response)))
                        },
                    )
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
    pub backend_url: String,
}

impl<T> hyper::service::Service<T> for ServiceBuilder {
    type Response = Service;
    type Error = hyper::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, _: &mut Context) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, _: T) -> Self::Future {
        let backend_url = self.backend_url.clone();
        let future = async move { Ok(Service { backend_url }) };
        Box::pin(future)
    }
}
