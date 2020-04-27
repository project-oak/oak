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

use hyper::Server;
use log::info;
use structopt::StructOpt;
use tokio::sync::{mpsc, oneshot};

mod auth_client;
mod redirect_handler;

#[derive(StructOpt, Clone)]
#[structopt(about = "OpenID Connect Client Example.")]
pub struct Opt {
    #[structopt(
        long,
        help = "Address of the Oak application to connect to.",
        default_value = "https://127.0.0.1:8080"
    )]
    address: String,
    #[structopt(
        long,
        help = "Address of the authentication server.",
        default_value = "https://localhost:8081"
    )]
    auth_server: String,
    #[structopt(
        long,
        help = "Address to listen on for the OAuth redirect.",
        default_value = "127.0.0.1:8089"
    )]
    redirect_address: String,
    #[structopt(
        long,
        help = "Path to the PEM-encoded CA root certificate.",
        default_value = "examples/certs/local/ca.pem"
    )]
    ca_cert: String,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let opt = Opt::from_args();
    let mut runner = tokio::runtime::Runtime::new().unwrap();
    let request_url = runner.block_on(auth_client::get_authentication_request_url(
        &opt.ca_cert,
        &opt.auth_server,
        &opt.redirect_address,
    ))?;
    let code = runner.block_on(get_authentication_code(&opt.redirect_address, &request_url))?;
    info!("Received code: {}", code);
    Ok(())
}

/// Gets the OIDC authentication code by opening the default browser and extracting it from the
/// resulting redirect URL.
async fn get_authentication_code(
    redirect_address: &str,
    request_url: &str,
) -> Result<String, Box<dyn std::error::Error>> {
    let (shutdown_sender, shutdown_receiver) = oneshot::channel();
    let (result_sender, mut result_receiver) = mpsc::channel(1);
    let producer = redirect_handler::RedirectHandlerProducer::new(result_sender);

    let redirect_address = redirect_address.parse()?;
    info!("Listening for redirect on {}", &redirect_address);
    let task = tokio::spawn(async move {
        Server::bind(&redirect_address)
            .serve(producer)
            // Use oneshot channel as signal for shutdown.
            .with_graceful_shutdown(async move {
                shutdown_receiver.await.unwrap();
            })
            .await
            .unwrap();
    });

    info!("Opening Auth request in Browser");
    info!("URL: {}", &request_url);
    // Open the URL in the system-configured default browser.
    open::that(request_url)?;

    // Wait for result sent by redirect handler.
    let result = result_receiver.recv().await;
    result_receiver.close();

    // Notify local HTTP server to shutdown.
    shutdown_sender.send(()).unwrap();

    // Wait until graceful shutdown is completed, ignoring shutdown errors.
    task.await.ok();
    let code = result.unwrap().unwrap();
    Ok(code)
}
