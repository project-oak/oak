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

use futures::channel::oneshot::{self, Sender};
use futures_util::future;
use hyper::{service::Service, Body, Request, Response, Server, StatusCode};
use log::{info, warn};
use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
    task::{Context, Poll},
};
use structopt::StructOpt;
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

    let (sender, receiver) = oneshot::channel();
    let result_sender = Arc::new(Mutex::new(ResultSender {
        sender: Some(sender),
        result: None,
    }));
    let maker = MakeHandler {
        result_sender: result_sender.clone(),
    };

    let mut runner = tokio::runtime::Runtime::new().unwrap();
    let task = runner.spawn(async move {
        Server::bind(&redirect_address)
            .serve(maker)
            // Use oneshot channel as signal for shutdown.
            .with_graceful_shutdown(async move {
                receiver.await.unwrap();
            })
            .await
    });

    let request_uri = get_authentication_request_url(opt);
    info!("Opening Auth request in Browser");
    info!("URI: {}", &request_uri);
    // Open the URL in the system-configured default browser.
    open::that(request_uri)?;

    // Wait until notified that the redirect has been processed.
    runner.block_on(task)??;

    let result = result_sender.lock().unwrap();
    let code = result.result.as_ref().unwrap().as_ref().ok().unwrap();
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
    let redirect_uri = format!("http://{}", opt.redirect_address);
    // TODO(#886): Retrieve state and code challenge from server and add to request.
    auth_endpoint
        .query_pairs_mut()
        .append_pair("scope", scope)
        .append_pair("response_type", "code")
        .append_pair("redirect_uri", &redirect_uri)
        .append_pair("client_id", &opt.client_id);
    auth_endpoint.to_string()
}

/// Provides storage for the result of proccessing the redirect and providing a notification to the
/// main thread that it has been processed.
///
/// The oneshot Sender can only be used once.
struct ResultSender {
    sender: Option<Sender<()>>,
    result: Option<Result<String, String>>,
}

impl ResultSender {
    fn notify(&mut self) {
        if self.sender.is_some() {
            self.sender.take().unwrap().send(()).unwrap();
        }
    }
}

/// Handles the redirects to extract code from the query string.
///
/// A new instance is created for every incoming request. The redirect URL contains the result of
/// the authentication as query string parameters. If the the authentication is successful the
/// authentication code is be passed in the `code` paramter. If it failed the reason is passed in
/// the `error` paramter.
///
/// The ResultSender is used to communicate the results back to the main thread and to notify Hyper
/// to gracefully shut down the web server via the oneshot channel.
///
/// The handler is also responsible for sending an appropriate response to the client browser.
struct RedirectHandler {
    result_sender: Arc<Mutex<ResultSender>>,
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
            let result_sender = &mut self.result_sender.lock().unwrap();
            if let Some(code) = lookup.get("code") {
                let code = code.to_string();
                info!("Auth code: {:?}", code);
                result_sender.result = Some(Ok(code));
                result_sender.notify();
                future::ok(Response::new(Body::from("Success!")))
            } else if let Some(error) = lookup.get("error") {
                let error = error.to_string();
                warn!("Error: {:?}", error);
                result_sender.result = Some(Ok(error));
                result_sender.notify();
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
struct MakeHandler {
    result_sender: Arc<Mutex<ResultSender>>,
}

impl<T> Service<T> for MakeHandler {
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
