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

//! Sends a gRPC request to the weather lookup app and checks the response has the correct format.

pub mod proto {
    tonic::include_proto!("oak.functions.server");
}

use crate::proto::grpc_handler_client::GrpcHandlerClient;

use anyhow::Context;
use http::uri::Uri;
use log::info;
use oak_functions_abi::proto::Request;
use regex::Regex;
use structopt::StructOpt;
use tonic::transport::Channel;

#[derive(StructOpt, Clone)]
#[structopt(about = "Weather Lookup Client")]
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

    // Create client
    let channel = Channel::builder(uri.clone()).connect().await?;
    let mut client = GrpcHandlerClient::new(channel);

    // create and send a request
    let content = br#"{"lat":52,"lon":0}"#.to_vec();
    let req = tonic::Request::new(Request { content });

    let res = client.invoke(req).await.context("Error sending request ")?;
    info!("Received response: {:?}", res.get_ref());
    let res = res.into_inner();
    let body = std::str::from_utf8(res.body().unwrap()).unwrap();
    let re = Regex::new(r#"\{"temperature_degrees":.*\}"#).unwrap();
    assert!(re.is_match(body));

    Ok(())
}
