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

use futures_util::future;
use hyper::{service::Service, Body, Request, Response, StatusCode};
use log::{info, warn};
use std::{
    collections::HashMap,
    error, fmt,
    task::{Context, Poll},
};
use tokio::sync::mpsc::Sender;
use url::form_urlencoded;

/// Handles the redirects to extract code from the query string.
///
/// A new instance is created for every incoming request. The redirect URL contains the result of
/// the authentication as query string parameters. If the the authentication is successful the
/// authentication code is passed in the `code` parameter. If it failed the reason is passed in
/// the `error` parameter.
///
/// The `result_sender` is used to communicate the results back to the main function.
///
/// The handler is responsible for sending an appropriate response to the client browser.
pub struct RedirectHandler {
    result_sender: Sender<Result<String, AuthError>>,
}

impl Service<Request<Body>> for RedirectHandler {
    type Response = Response<Body>;
    type Error = hyper::Error;
    type Future = future::Ready<Result<Self::Response, Self::Error>>;

    fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Ok(()).into()
    }

    fn call(&mut self, request: Request<Body>) -> Self::Future {
        if let Some(query) = request.uri().query() {
            let lookup: HashMap<_, _> = form_urlencoded::parse(query.as_bytes()).collect();
            if let Some(code) = lookup.get("code") {
                let code = code.to_string();
                info!("Auth code: {:?}", code);
                self.result_sender.try_send(Ok(code)).unwrap();
                future::ok(Response::new(Body::from("Success!")))
            } else if let Some(error) = lookup.get("error") {
                let error = error.to_string();
                warn!("Error: {:?}", error);
                self.result_sender
                    .try_send(Err(AuthError::new(&error)))
                    .unwrap();
                future::ok(
                    Response::builder()
                        .status(StatusCode::UNAUTHORIZED)
                        .body(Body::from("Authentication failed!"))
                        .unwrap(),
                )
            } else {
                future::ok(
                    Response::builder()
                        .status(StatusCode::BAD_REQUEST)
                        .body(Body::from("Invalid query string!"))
                        .unwrap(),
                )
            }
        } else {
            future::ok(
                Response::builder()
                    .status(StatusCode::BAD_REQUEST)
                    .body(Body::from("No query string!"))
                    .unwrap(),
            )
        }
    }
}

/// Produces instances of the redirect handler service.
///
/// Hyper uses it to create a new handler for every incoming request. The handler needs a copy of
/// the reference to the ResultSender to communicate the results back to the main thread.
pub struct RedirectHandlerProducer {
    result_sender: Sender<Result<String, AuthError>>,
}

impl RedirectHandlerProducer {
    pub fn new(result_sender: Sender<Result<String, AuthError>>) -> RedirectHandlerProducer {
        RedirectHandlerProducer { result_sender }
    }
}

impl<T> Service<T> for RedirectHandlerProducer {
    type Response = RedirectHandler;
    type Error = std::io::Error;
    type Future = future::Ready<Result<Self::Response, Self::Error>>;

    fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Ok(()).into()
    }

    fn call(&mut self, _: T) -> Self::Future {
        future::ok(RedirectHandler {
            result_sender: self.result_sender.clone(),
        })
    }
}

/// Wrapper to store the server authentication error message.
#[derive(Debug, Clone)]
pub struct AuthError {
    server_message: String,
}

impl AuthError {
    pub fn new(message: &str) -> AuthError {
        AuthError {
            server_message: message.to_owned(),
        }
    }
}

impl fmt::Display for AuthError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Authentication error: {}", &self.server_message)
    }
}

impl error::Error for AuthError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        // Source is not tracked.
        None
    }
}
