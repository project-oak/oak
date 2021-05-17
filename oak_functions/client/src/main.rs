//
// Copyright 2021 The Project Oak Authors
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

//! Sends a gRPC request to the weather lookup application and checks that the response has the
//! correct format.

pub mod proto {
    tonic::include_proto!("oak.functions.server");
}

use crate::proto::grpc_handler_client::GrpcHandlerClient;

use anyhow::Context;
use http::uri::Uri;
use oak_functions_abi::proto::Request;
use std::io::Read;
use structopt::StructOpt;
use tonic::transport::Channel;

#[derive(StructOpt, Clone)]
#[structopt(about = "Oak Functions Client")]
pub struct Opt {
    #[structopt(
        long,
        help = "URI of the Oak Functions application to connect to",
        default_value = "http://localhost:8080"
    )]
    uri: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();
    let uri: Uri = opt.uri.parse().context("Error parsing URI")?;

    // Create client.
    let channel = Channel::builder(uri.clone()).connect().await?;
    let mut client = GrpcHandlerClient::new(channel);

    // Create and send request.
    let mut request_body = Vec::new();
    std::io::stdin()
        .read_to_end(&mut request_body)
        .context("Could not read request from STDIN")?;
    let req = tonic::Request::new(Request { body: request_body });

    let res = client.invoke(req).await.context("Error sending request")?;
    let res = res.into_inner();
    let response_body = std::str::from_utf8(res.body().unwrap()).unwrap();
    print!("{}", response_body);

    Ok(())
}
