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

//! Sends a gRPC request to an Oak Functions application and checks that the response has the
//! correct format.

use anyhow::Context;
use oak_functions_abi::proto::{ConfigurationInfo, Request};
use oak_functions_client::Client;
use regex::Regex;
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
    /// Optional, only for testing.
    #[structopt(long, help = "expected response body, for testing")]
    expected_response_pattern: Option<String>,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    // TODO(#2348): Replace with a more flexible specification of the verification logic.
    // For the common client used in examples, we expect ML-inference and private metrics to be
    // disabled.
    let config_verifier = |config: ConfigurationInfo| {
        if config.ml_inference {
            anyhow::bail!("ML-inference support is enabled")
        }
        if config.metrics.is_some() {
            anyhow::bail!("private metrics support is enabled")
        }
        Ok(())
    };

    let mut client = Client::new(&opt.uri, config_verifier)
        .await
        .context("Could not create Oak Functions client")?;

    let request = Request {
        body: opt.request.as_bytes().to_vec(),
    };

    let response = client
        .invoke(request)
        .await
        .context("Could not invoke Oak Functions")?;

    let response_body = std::str::from_utf8(response.body().unwrap()).unwrap();
    match opt.expected_response_pattern {
        Some(expected) => {
            let re = Regex::new(&expected).unwrap();
            assert!(re.is_match(response_body));
        }
        None => println!("{}", response_body),
    }

    Ok(())
}
