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

//! Sends 200 requests to the metrics backend alternating between "a" and "b".

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

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();

    let mut client = Client::new(&opt.uri, |_config| Ok(()))
        .await
        .context("Could not create Oak Functions client")?;

    for i in 0..200 {
        let body = if i % 2 == 0 { b"a" } else { b"b" };
        let request = Request {
            body: body.to_vec(),
        };

        client
            .invoke(request)
            .await
            .context("Could not invoke Oak Functions")?;
    }
    Ok(())
}
