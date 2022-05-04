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
use futures::future::join_all;
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
    #[structopt(long, help = "The QPS to simulate", default_value = "10")]
    qps: u32,
    #[structopt(
        long,
        help = "How many rounds, i.e., seconds, we sent requests",
        default_value = "1"
    )]
    rounds: u32,
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() -> anyhow::Result<()> {
    env_logger::builder()
        .format_timestamp(None)
        .format_level(false)
        .format_module_path(false)
        .format_target(false)
        .init();
    let opt = Opt::parse();

    let target_qps = opt.qps;
    let rounds = opt.rounds;

    // Currently every client sends only one request and terminates.
    let mut clients = vec![];

    let start_time = Instant::now();

    for (n, p) in // (1..(target_qps * rounds)).enumerate()
        Sieve::new()
            .iter()
            .take((target_qps * rounds) as usize)
            .enumerate()
    {
        let server_url = opt.server_url.clone();

        // We currently spawn a new client for every new request. Alternatively we could re-use the
        // client for every round.
        clients.push(tokio::spawn(async move {
            let request = format!("{}", p);
            let request_sent = start_time.elapsed();
            log::info!("Client Request {}: {}", p, request_sent.as_millis());

            let url = format!("{}/request", server_url);
            let response = send_request(&url, Method::POST, request.as_bytes())
                .await
                .context("Couldn't receive response")
                .unwrap();

            let response_received = start_time.elapsed();

            // We don't check whether response is exepected response.
            let _parsed_response =
                String::from_utf8(response).context("Couldn't decode response body");

            log::info!("Client Response {}: {}", p, response_received.as_millis(),);
            response_received - request_sent
        }));

        // Compute current round from queries already sent.
        let current_round = n as u32 / target_qps;

        // Adapt the sleep_time depending on how many queries still have to fit.
        let queries_sent_this_round = (n + 1) as u32 % target_qps;
        let queries_still_to_fit_this_round = target_qps - queries_sent_this_round;

        let time_elapsed_this_round = Duration::checked_sub(
            start_time.elapsed(),
            Duration::from_secs(current_round as u64),
        )
        .expect("The time elapsed is shorter than current round.");

        // If there is no time left, we set time_still_left to 0.
        let time_still_left_this_round =
            Duration::checked_sub(Duration::from_secs(1), time_elapsed_this_round)
                .unwrap_or(Duration::from_secs(0));

        // If there are no queries still to fit in this round and there is time left in the round,
        // we sleep until the second has elapsed.
        let delta = time_still_left_this_round
            .checked_div(queries_still_to_fit_this_round)
            .unwrap_or_else(|| {
                Duration::checked_sub(Duration::from_secs(1), time_elapsed_this_round)
                    .unwrap_or(Duration::from_secs(0))
            });

        sleep(delta).await;
    }

    // Estimate how many qps we actually achieved by checking how much time we spent between
    // starting and ending the loop.
    let actual_time_taken = &start_time.elapsed();
    log::info!("Actual time taken {:?}", actual_time_taken);

    let mut total_delay = Duration::from_secs(0);
    for duration in join_all(clients).await {
        total_delay = total_delay + duration.unwrap()
    }
    let avg_delay = total_delay / (target_qps * rounds);

    println!("{:?},{:?}", actual_time_taken, avg_delay);

    Ok(())
}
