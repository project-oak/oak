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

//! Backend server for the Aggregator example.
//!
//! Backend is used in tests/experiments and is represented as a gRPC server that listens for
//! samples provided by the Aggregator and prints them into the standard output.

pub mod proto {
    tonic::include_proto!("oak.examples.aggregator");
}

use log::info;
use proto::{
    aggregator_server::{Aggregator, AggregatorServer},
    Sample,
};
use structopt::StructOpt;
use tonic::{
    transport::{Identity, Server, ServerTlsConfig},
    Request, Response, Status,
};

#[derive(StructOpt, Clone)]
#[structopt(about = "Aggregator Backend")]
pub struct Opt {
    #[structopt(long, help = "Private RSA key file used by gRPC server.")]
    grpc_tls_private_key: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS certificate file used by gRPC server."
    )]
    grpc_tls_certificate: String,
}

#[derive(Default)]
pub struct AggregatorBackend;

#[tonic::async_trait]
impl Aggregator for AggregatorBackend {
    async fn submit_sample(&self, req: Request<Sample>) -> Result<Response<()>, Status> {
        let sample = req.into_inner();
        info!(
            "Received sample: bucket={}, data={:?}",
            sample.bucket, sample.data
        );
        Ok(Response::new(()))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let opt = Opt::from_args();

    let private_key = tokio::fs::read(&opt.grpc_tls_private_key).await?;
    let certificate = tokio::fs::read(&opt.grpc_tls_certificate).await?;

    let identity = Identity::from_pem(certificate, private_key);

    let address = "[::]:8888".parse()?;
    let handler = AggregatorBackend::default();

    info!("Starting the backend server at {:?}", address);

    Server::builder()
        .tls_config(ServerTlsConfig::new().identity(identity))
        .add_service(AggregatorServer::new(handler))
        .serve(address)
        .await?;

    Ok(())
}
