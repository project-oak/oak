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

//! Backend server for the Trusted Shuffler example.

use anyhow::Context;
use clap::Parser;
use futures_util::FutureExt;
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Method, Request, Response, Server, StatusCode,
};
use log::info;

#[derive(Parser, Clone)]
#[clap(about = "Backend for Trusted Shuffler Example")]
pub struct Opt {
    #[structopt(
        long,
        help = "Address to listen on for the HTTP server",
        default_value = "[::]:8888"
    )]
    listen_address: String,
}

async fn handler(request: Request<Body>) -> Result<Response<Body>, hyper::Error> {
    match (request.method(), request.uri().path()) {
        (&Method::POST, "/request") => {
            let body = hyper::body::to_bytes(request.into_body()).await?;
            info!("Received request: {:?}", body);
            // Send back the response body.
            Ok(Response::new(Body::from(body)))
        }

        _ => {
            let mut not_found = Response::default();
            *not_found.status_mut() = StatusCode::NOT_FOUND;
            Ok(not_found)
        }
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::parse();

    let address = opt
        .listen_address
        .parse()
        .context("Couldn't parse address")?;

    let service = make_service_fn(|_| async { Ok::<_, hyper::Error>(service_fn(handler)) });

    info!("Starting the backend server at {:?}", address);
    let server = Server::bind(&address).serve(service);

    tokio::select!(
        result = server => {
            result.context("Couldn't run server")?;
        },
        () = tokio::signal::ctrl_c().map(|r| r.unwrap()) => {
            info!("Stopping the backend server");
        },
    );

    Ok(())
}
