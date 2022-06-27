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

use anyhow::Context;
use clap::Parser;
use grpc_unary_attestation::client::AttestationClient;
use std::io::{stdin, BufRead};

#[derive(Parser, Debug)]
struct Args {
    /// Address of the server.
    #[clap(long, default_value = "http://127.0.0.1:8000")]
    server: String,

    /// Message to be sent to the server. If not specified (with a response and number of
    /// iterations), uses stdio.
    #[clap(long, requires_all = &["expected-response", "iterations"])]
    request: Option<String>,

    /// Expected response from the server. If not specified (with a request and number of
    /// iterations), uses stdio.
    #[clap(long, requires_all = &["request", "iterations"])]
    expected_response: Option<String>,

    /// Number of times the request should be sent, and the expected response validated.
    #[clap(long, requires_all = &["request", "expected-response"])]
    iterations: Option<usize>,

    /// Test sending a large message
    #[clap(long, conflicts_with_all = &["request", "expected-response", "iterations"])]
    test_large_message: bool,
}

async fn chat(client: &mut AttestationClient, message: String) -> anyhow::Result<String> {
    let response = client
        .send(message.as_bytes())
        .await
        .context("Error invoking Oak Functions instance")?;

    String::from_utf8(response).map_err(Into::into)
}

const TWO_MIB: usize = 2097000;
const LARGE_MESSAGE: [u8; TWO_MIB] = [0; TWO_MIB];

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Args::parse();

    let mut client = AttestationClient::create(&cli.server)
        .await
        .context("Could not create client")?;

    match (
        cli.test_large_message,
        cli.request,
        cli.expected_response,
        cli.iterations,
    ) {
        (true, None, None, None) => {
            // The client should be a able to send a large message without
            // crashing or hanging.
            let response = client
                .send(&LARGE_MESSAGE)
                .await
                .context("Error invoking Oak Functions instance");
            assert!(response.is_ok());
        }
        (false, Some(request), Some(expected_response), Some(iterations)) => {
            for _ in 0..iterations {
                let response = chat(&mut client, request.clone()).await?;
                assert_eq!(response, expected_response);
            }
        }
        _ => {
            let mut lines = stdin().lock().lines();
            while let Some(Ok(line)) = lines.next() {
                let response = chat(&mut client, line).await?;
                println!("Response: {:?}", response);
            }
        }
    }
    Ok(())
}
