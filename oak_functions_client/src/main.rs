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

//! Sends a gRPC request to an Oak Functions application and checks that the
//! response has the correct format.

use anyhow::Context;
use clap::Parser;
use http::uri::Uri;
use oak_client::verifier::InsecureAttestationVerifier;
use oak_functions_abi::Request;
use oak_functions_client::OakFunctionsClient;
use regex::Regex;

static TWO_MIB: usize = 2 * 1024 * 1024;
static LARGE_MESSAGE: [u8; TWO_MIB] = [0; TWO_MIB];

#[derive(Parser, Clone)]
#[command(about = "Oak Functions Client")]
pub struct Opt {
    #[arg(
        long,
        help = "URI of the Oak Functions application to connect to",
        default_value = "http://localhost:8080"
    )]
    uri: String,

    #[arg(long, help = "request payload", required_unless_present = "test_large_message")]
    request: Option<String>,

    /// Optional, only for testing.
    #[arg(long, help = "expected response body, for testing")]
    expected_response_pattern: Option<String>,

    /// Number of times the request should be sent, and the expected response
    /// validated.
    #[arg(long, requires_all = &["request", "expected_response_pattern"])]
    iterations: Option<usize>,

    /// Test sending a large message
    #[arg(long, conflicts_with_all = &["request", "expected_response_pattern", "iterations"])]
    test_large_message: bool,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::parse();

    let mut client =
        OakFunctionsClient::new(Uri::try_from(opt.uri).unwrap(), &InsecureAttestationVerifier {})
            .await
            .context("couldn't create Oak Functions client")?;

    if opt.test_large_message {
        // The client should be a able to send a large message without
        // crashing or hanging.
        let response = client.invoke(&LARGE_MESSAGE).await;
        assert!(response.is_ok());
        return Ok(());
    }

    let iterations = opt.iterations.unwrap_or(1);

    let request = opt.request.unwrap();

    println!("req: {:?}", Request { body: request.as_bytes().to_vec() });

    for _ in 0..iterations {
        let response = client.invoke(request.as_bytes()).await?;

        println!("Response: {:?}", response);
        let response_body = std::str::from_utf8(&response).unwrap();
        println!("Response: {:?}", response_body);
        if let Some(ref expected) = opt.expected_response_pattern {
            let re = Regex::new(expected).unwrap();
            assert!(re.is_match(response_body));
        }
    }

    Ok(())
}
