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
use trusted_shuffler_common::{send_grpc_request, send_request};

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
        help = "How many seconds the clients sent requests. Otherwise the Trusted Shuffler gets stuck because the last batch does not reach k requests.",
        default_value = "1"
    )]
    seconds: u32,
}

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    env_logger::builder()
        .format_timestamp(None)
        .format_level(false)
        .format_module_path(false)
        .format_target(false)
        .init();
    let opt = Opt::parse();

    let target_qps = opt.qps;
    let seconds = opt.seconds;

    // Currently every client sends only one request and terminates.
    let mut clients = vec![];

    let start_time = Instant::now();

    for (n, prime) in Sieve::new()
        .iter()
        .take((target_qps * seconds) as usize)
        .enumerate()
    {
        let server_url = opt.server_url.clone();

        // We currently spawn a new client for every new request. Alternatively we could re-use the
        // client for every round.
        clients.push(tokio::spawn(async move {
            grpc_request(prime, server_url, start_time).await
            // http_request(prime, server_url, start_time).await
        }));

        // Compute current round from queries already sent.
        let current_round = n as u32 / target_qps;

        // Adapt the sleep_time depending on how many queries still have to fit.
        let queries_sent_this_round = (n + 1) as u32 % target_qps;
        let queries_still_to_fit_this_round = target_qps - queries_sent_this_round;

        // If more than one maximal time in this round elapsed, we set to the maximal time per
        // round. The maximal time is one second.
        let time_elapsed_this_round = Duration::checked_sub(
            start_time.elapsed(),
            Duration::from_secs(current_round as u64),
        )
        .unwrap_or(Duration::from_secs(1));

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

        // Note: If we remove this sleep, the clients crash.
        sleep(delta).await;
    }

    // Estimate how many qps we actually achieved by checking how much time we spent between
    // starting and ending the loop.
    let actual_time_taken = &start_time.elapsed();
    log::info!("Actual time taken {:?}", actual_time_taken);

    // Initialize total_delay and
    let mut total_delay = Duration::from_secs(0);
    let mut max_delay = Duration::from_secs(0);

    for duration in join_all(clients).await {
        let duration = duration.unwrap();
        total_delay += duration;
        if duration > max_delay {
            max_delay = duration;
        }
    }
    let avg_delay = total_delay / (target_qps * seconds);

    // For every call to clients we measure the actual time, the avg delay and the max delay.
    println!(
        "{:?},{:?},{:?}",
        actual_time_taken,
        avg_delay.as_millis(),
        max_delay.as_millis()
    );

    Ok(())
}

// Send a HTTP request of `prime_to_send` to `server_url` taking time measurement from
// `start_time` and return duration until response is received.
async fn http_request(prime_to_send: u64, server_url: String, start_time: Instant) -> Duration {
    {
        let request = format!("{}", prime_to_send);
        let request_sent = start_time.elapsed();
        log::info!("Client Request {}", prime_to_send);

        let url = format!("{}/request", server_url);
        let response = send_request(&url, Method::POST, request.as_bytes())
            .await
            .context("Couldn't receive response");

        let response_received = start_time.elapsed();

        let parsed_response =
            String::from_utf8(response.unwrap()).context("Couldn't decode response body");

        assert_eq!(parsed_response.unwrap(), prime_to_send.to_string());

        log::info!(
            "Client Response {}: {:?}",
            prime_to_send,
            response_received - request_sent,
        );
        response_received - request_sent
    }
}

// Send a gRPC request of `prime_to_send` to `server_url` taking time measurement from
// `start_time` and return duration until response is received.
async fn grpc_request(prime_to_send: u64, server_url: String, start_time: Instant) -> Duration {
    {
        let request = format!("{}", prime_to_send);
        let request_sent = start_time.elapsed();
        log::info!("Client Request {}", prime_to_send);

        let url = format!("{}", server_url);
        let response = send_grpc_request(url.clone(), request.as_bytes())
            .await
            .context("Couldn't receive response");

        let response_received = start_time.elapsed();

        let parsed_response =
            String::from_utf8(response.unwrap()).context("Couldn't decode response body");

        assert_eq!(parsed_response.unwrap(), prime_to_send.to_string());

        log::info!(
            "Client Response {}: {:?}",
            prime_to_send,
            response_received - request_sent,
        );
        response_received - request_sent
    }
}
