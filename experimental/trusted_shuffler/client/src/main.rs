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

//! Client for the Trusted Shuffler example.

use anyhow::Context;
use clap::Parser;
use hyper::Method;
use log::info;
use std::time::Instant;
use trusted_shuffler_common::send_request;

#[derive(Parser, Clone)]
#[clap(about = "Client for Trusted Shuffler Example")]
pub struct Opt {
    #[structopt(
        long,
        help = "URL of the Trusted Shuffler HTTP service to connect to",
        default_value = "http://localhost:8080"
    )]
    server_url: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::parse();

    let request = "Request 1";
    info!("Sending request: {}", request);
    let url = format!("{}/request", &opt.server_url);

    let request_start = Instant::now();
    let response = send_request(&url, Method::POST, request.as_bytes())
        .await
        .context("Couldn't receive response")?;
    let request_duration = request_start.elapsed();

    let parsed_response = String::from_utf8(response).context("Couldn't decode response body")?;
    info!(
        "Received response: {} in {:?}",
        parsed_response, request_duration
    );
    Ok(())
}
