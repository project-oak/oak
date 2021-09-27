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

//! Oak Functions Hello World example client.

use anyhow::Context;
use oak_functions_abi::proto::Request;
use oak_functions_client::Client;
use structopt::StructOpt;

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

const CLIENT_HELLO_WORLD: &str = "Client Hello World";
const SERVER_HELLO_WORLD: &str = "Server Hello World";

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let mut client = Client::new(&opt.uri)
        .await
        .context("Couldn't create Oak Functions client")?;

    let request = Request {
        body: CLIENT_HELLO_WORLD.as_bytes().to_vec(),
    };

    let response = client
        .invoke(request)
        .await
        .context("Couldn't invoke Oak Functions")?;
    let response_body = response.body().context("Couldn't read response body")?;

    let parsed_response =
        std::str::from_utf8(response_body).context("Couldn't parse response body")?;
    assert_eq!(parsed_response, SERVER_HELLO_WORLD);

    Ok(())
}
