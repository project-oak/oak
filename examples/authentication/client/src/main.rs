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

//! Example client authenticating to Oak using OpenID Connect.
//!
//! This example uses the Google Identity Platform.
//! https://developers.google.com/identity/

use futures_util::future;
use hyper::{service::Service, Body, Request, Response, Server, StatusCode};
use log::{info, warn};
use std::{
    collections::HashMap,
    task::{Context, Poll},
};
use structopt::StructOpt;
use tokio::sync::{
    mpsc::{self, Sender},
    oneshot,
};
use url::{form_urlencoded, Url};

#[derive(StructOpt, Clone)]
#[structopt(about = "OpenID Connect Client Example.")]
pub struct Opt {
    #[structopt(
        long,
        help = "Address of the Oak application to connect to.",
        default_value = "127.0.0.1:8080"
    )]
    address: String,
    #[structopt(
        long,
        help = "Address to listen on for the OAuth redirect.",
        default_value = "127.0.0.1:8089"
    )]
    redirect_address: String,
    #[structopt(long, help = "Path to the PEM-encoded CA root certificate.")]
    ca_cert: Option<String>,
    // TODO(#886): Retrieve client_id from server, rather than flag.
    #[structopt(long, help = "The OAuth client ID.")]
    client_id: String,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let opt = Opt::from_args();
    let redirect_address = opt.redirect_address.parse()?;
    info!("Listening for redirect on {}", &redirect_address);

    let (shutdown_sender, shutdown_receiver) = oneshot::channel();
    let (result_sender, mut result_receiver) = mpsc::channel(1);
    let producer = RedirectHandlerProducer { result_sender };

    let mut runner = tokio::runtime::Runtime::new().unwrap();
    let task = runner.spawn(async move {
        Server::bind(&redirect_address)
            .serve(producer)
            // Use oneshot channel as signal for shutdown.
            .with_graceful_shutdown(async move {
                shutdown_receiver.await.unwrap();
            })
            .await
            .unwrap();
    });

    let request_url = get_authentication_request_url(opt);
    info!("Opening Auth request in Browser");
    info!("URL: {}", &request_url);
    // Open the URL in the system-configured default browser.
    open::that(request_url)?;

    // Wait for result sent by redirect handler.
    let result = runner.block_on(result_receiver.recv());
    result_receiver.close();

    // Notify server to shutdown.
    shutdown_sender.send(()).unwrap();

    // Wait until graceful shutdown is completed..
    runner.block_on(task)?;

    let code = result.unwrap().unwrap();
    info!("Received code: {}", code);
    Ok(())
}

/// Gets the URL for authentication requests.
///
/// See: https://developers.google.com/identity/protocols/oauth2/openid-connect#sendauthrequest
/// for more details on the request URL for the Google Identity Platform.
fn get_authentication_request_url(opt: Opt) -> String {
    // TODO(#886): Retrieve endpoint from server.
    let mut auth_endpoint = Url::parse("https://accounts.google.com/o/oauth2/v2/auth").unwrap();
    // TODO(#886): Consider retrieving scope from server.
    let scope = "openid email";
    let redirect_url = format!("http://{}", opt.redirect_address);
    // TODO(#886): Retrieve state and code challenge from server and add to request.
    auth_endpoint
        .query_pairs_mut()
        .append_pair("scope", scope)
        .append_pair("response_type", "code")
        .append_pair("redirect_uri", &redirect_url)
        .append_pair("client_id", &opt.client_id);
    auth_endpoint.to_string()
}

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
struct RedirectHandler {
    result_sender: Sender<Result<String, String>>,
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
                self.result_sender.try_send(Err(error)).unwrap();
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
struct RedirectHandlerProducer {
    result_sender: Sender<Result<String, String>>,
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
