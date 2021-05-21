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

use anyhow::Context;
use http::uri::Uri;
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
    #[structopt(long, help = "request payload")]
    request: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();
    let uri: Uri = opt.uri.parse().context("Error parsing URI")?;

    let mut client = Client::new(&uri)
        .await
        .context("Could not create Oak Functions client")?;

    let response = client
        .invoke(opt.request.as_bytes())
        .await
        .context("Could not invoke Oak Functions")?;
    let response_body = std::str::from_utf8(response.body().unwrap()).unwrap();
    print!("{}", response_body);

    Ok(())
}
