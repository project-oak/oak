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

pub mod proto {
    tonic::include_proto!("oak.examples.aggregator");
}

use proto::aggregator_server::{Aggregator, AggregatorServer};
use proto::Sample;
use tonic::{transport::Server, Request, Response, Status};

#[derive(Default)]
pub struct AggregatorBackend;

#[tonic::async_trait]
impl Aggregator for AggregatorBackend {
    async fn submit_sample(&self, req: Request<Sample>) -> Result<Response<()>, Status> {
        let sample = req.into_inner();
        println!(
            "Aggregation: bucket={}, data={:?}",
            sample.bucket, sample.data
        );
        Ok(Response::new(()))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let address = "[::]:8888".parse()?;
    let handler = AggregatorBackend::default();

    println!("Starting the backend server at {:?}", address);

    Server::builder()
        .add_service(AggregatorServer::new(handler))
        .serve(address)
        .await?;

    Ok(())
}
