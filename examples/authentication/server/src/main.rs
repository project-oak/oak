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

//! Example implemenation of an OpenID Connect authentication server.
//!
//! This example uses the Google Identity Platform.
//! https://developers.google.com/identity/
//!
//! The additional authentication server is primarily used so that we do not have to expose the
//! client secret to the client app, where it could be extracted.

use log::info;
use structopt::StructOpt;
use tonic::transport::{Identity, Server, ServerTlsConfig};

pub mod proto {
    tonic::include_proto!("oak.examples.authentication");
}

mod auth_handler;
mod token_exchanger;

#[derive(StructOpt, Clone)]
#[structopt(about = "OpenID Connect Server Example.")]
pub struct Opt {
    #[structopt(
        long,
        help = "Address to listen on for client connections.",
        default_value = "127.0.0.1:8081"
    )]
    address: String,
    #[structopt(long, help = "The OAuth client ID.")]
    client_id: String,
    #[structopt(long, help = "The OAuth client secret.")]
    client_secret: String,
    #[structopt(
        long,
        help = "The path to the PEM-encoded TLS certificate.",
        default_value = "examples/certs/local/local.pem"
    )]
    cert: String,
    #[structopt(
        long,
        help = "The path to the private key for the TLS certificate.",
        default_value = "examples/certs/local/local.key"
    )]
    private_key: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let opt = Opt::from_args();
    let address = opt.address.parse()?;
    let cert = tokio::fs::read(opt.cert).await?;
    let key = tokio::fs::read(opt.private_key).await?;
    let identity = Identity::from_pem(cert, key);
    info!("Starting the auth server at {:?}", address);

    Server::builder()
        .tls_config(ServerTlsConfig::new().identity(identity))
        .add_service(auth_handler::build_service(
            &opt.client_id,
            &opt.client_secret,
        ))
        .serve(address)
        .await?;

    Ok(())
}
