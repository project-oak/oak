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
use primes::{PrimeSet, Sieve};
use std::time::{Duration, Instant};
use tokio::time::sleep;
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
    #[structopt(long, help = "The QPS we are aiming to simulate", default_value = "10")]
    qps: u32,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::parse();

    let expected_qps = opt.qps;

    // Give 10 ms lee-way for stuff. Distribute the qps evently over the remaining 900 ms.
    let sleep_between_qs = 900 / expected_qps;

    // Start with giving one second iterations.
    let start_time = Instant::now();

    //
    eprintln!("phase,id,request_elapsed_in_ms,response_elapsed_in_ms");

    for p in Sieve::new().iter().take(expected_qps as usize) {
        let server_url = opt.server_url.clone();

        tokio::spawn(async move {
            let request = format!("{}", p);
            let request_start = start_time.elapsed();

            let url = format!("{}/request", server_url);
            let response = send_request(&url, Method::POST, request.as_bytes())
                .await
                .context("Couldn't receive response");

            let request_duration = start_time.elapsed();

            if let Ok(response) = response {
                // We don't check whether response is exepected response.
                let _parsed_response =
                    String::from_utf8(response).context("Couldn't decode response body");

                eprintln!(
                    "client,{},{},{}",
                    p,
                    request_start.as_millis(),
                    request_duration.as_millis(),
                );
            }
        });
        sleep(Duration::from_millis(sleep_between_qs.into())).await;
    }

    // Estimate how many qps we actually achieved by checking how much time we spent between
    // starting and ending the loop.
    eprintln!("Actual time taken {:?}", &start_time.elapsed());

    Ok(())
}
