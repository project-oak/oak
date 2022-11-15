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
use echo::{
    echo_server::{Echo, EchoServer},
    EchoRequest, EchoResponse,
};
use futures_util::FutureExt;
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Method, Request, Response, Server, StatusCode,
};
use log::info;
use std::{net::SocketAddr, time::Instant};
use tonic::{transport::Server as TonicServer, Status};

pub mod echo {
    tonic::include_proto!("trusted_shuffler.proto.echo");
}

#[derive(Parser, Clone)]
#[command(about = "Backend for Trusted Shuffler Example")]
pub struct Opt {
    #[arg(
        long,
        help = "Address to listen on for the server",
        default_value = "[::]:8888"
    )]
    listen_address: String,
    #[arg(long, help = "Listen for gRPC requests")]
    use_grpc: bool,
}

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    env_logger::builder()
        .format_timestamp(None)
        .format_level(false)
        .format_module_path(false)
        .format_target(false)
        .init();
    let opt = Opt::parse();

    let address = opt
        .listen_address
        .parse()
        .context("couldn't parse address")?;

    if opt.use_grpc {
        start_grpc_backend(address).await
    } else {
        start_http_backend(address).await
    }
}

async fn start_http_backend(address: SocketAddr) -> anyhow::Result<()> {
    let service = make_service_fn(|_| async { Ok::<_, hyper::Error>(service_fn(handler)) });
    info!("Starting the HTTP backend server at {:?}", address);
    let server = Server::bind(&address).serve(service);

    tokio::select!(
        result = server => {
            result.context("couldn't run server")?;
        },
        () = tokio::signal::ctrl_c().map(|r| r.unwrap()) => {
            info!("Stopping the backend server");
        },
    );
    Ok(())
}

async fn handler(request: Request<Body>) -> Result<Response<Body>, hyper::Error> {
    match (request.method(), request.uri().path()) {
        (&Method::POST, "/request") => {
            let body = hyper::body::to_bytes(request.into_body()).await?;

            let request_start = Instant::now();
            log::info!(
                "Backend Request: {},{:?}",
                String::from_utf8(body.to_vec()).unwrap(),
                request_start,
            );

            // Currently we assume the backend takes no time, i.e., no time elapsed between request
            // and response.
            log::info!(
                "Backend Response: {},{:?}",
                String::from_utf8(body.to_vec()).unwrap(),
                request_start,
            );
            // Echo back the response body.
            Ok(Response::new(Body::from(body)))
        }

        _ => {
            let mut not_found = Response::default();
            *not_found.status_mut() = StatusCode::NOT_FOUND;
            Ok(not_found)
        }
    }
}

async fn start_grpc_backend(address: SocketAddr) -> anyhow::Result<()> {
    info!("Starting the gRPC backend server at {:?}", address);

    let echoer = MyEcho::default();
    let server = TonicServer::builder()
        .add_service(EchoServer::new(echoer))
        .serve(address);

    tokio::select!(
        result = server => {
            result.context("couldn't run server")?;
        },
        () = tokio::signal::ctrl_c().map(|r| r.unwrap()) => {
            info!("Stopping the backend server");
        },
    );

    Ok(())
}

#[derive(Debug, Default)]
pub struct MyEcho {}

#[tonic::async_trait]
impl Echo for MyEcho {
    async fn echo(
        &self,
        request: tonic::Request<EchoRequest>,
    ) -> Result<tonic::Response<EchoResponse>, Status> {
        let request = request.into_inner();

        let request_start = Instant::now();
        log::info!("Backend Request: {:?},{:?}", request, request_start);

        let echoed_value = request.value_to_echo;
        Ok(tonic::Response::new(EchoResponse { echoed_value }))
    }
}
