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

//! Oak Functions ABI test client.

use anyhow::Context;
use log::debug;
use oak_functions_abi::proto::{ConfigurationInfo, Request};
use oak_functions_abitest_common::*;
use oak_functions_client::Client;
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
#[structopt(about = "Oak Functions ABI test client.")]
pub struct Opt {
    #[structopt(
        long,
        help = "URI of the application to connect to",
        default_value = "http://localhost:8080/invoke"
    )]
    uri: String,
}

struct Test {
    name: String,
    expected_response: String,
}

impl Test {
    fn new(name: &str, expected_response: &str) -> Self {
        Self {
            name: name.to_string(),
            expected_response: expected_response.to_string(),
        }
    }
}

struct TestManager {
    uri: String,
    tests: Vec<Test>,
}

impl TestManager {
    fn new(uri: &str) -> Self {
        let mut tests = vec![];
        tests.push(Test::new(TEST_READ_WRITE, TEST_READ_WRITE_RESPONSE));
        tests.push(Test::new(TEST_DOUBLE_READ, TEST_DOUBLE_READ_RESPONSE));
        tests.push(Test::new(TEST_DOUBLE_WRITE, TEST_DOUBLE_WRITE_RESPONSE));
        tests.push(Test::new(TEST_WRITE_LOG, TEST_WRITE_LOG_RESPONSE));
        tests.push(Test::new(TEST_STORAGE_GET, TEST_STORAGE_GET_RESPONSE));

        Self {
            uri: uri.to_string(),
            tests,
        }
    }

    async fn run_tests(&self) -> anyhow::Result<()> {
        for test in &self.tests {
            self.run_test(&test.name, &test.expected_response)
                .await
                .context(format!("Couldn't run test: {}", &test.name))?;
        }
        Ok(())
    }

    async fn run_test(&self, test_name: &str, expected_response: &str) -> anyhow::Result<()> {
        let response = send_request(&self.uri, test_name)
            .await
            .context("Couldn't send request")?;
        assert_eq!(response, expected_response);
        debug!("{} test is successful", test_name);
        Ok(())
    }
}

async fn send_request(uri: &str, body: &str) -> anyhow::Result<String> {
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

    let mut client = Client::new(uri, config_verifier)
        .await
        .context("Couldn't create Oak Functions client")?;

    let request = Request {
        body: body.as_bytes().to_vec(),
    };

    let response = client
        .invoke(request)
        .await
        .context("Couldn't invoke Oak Functions")?;

    let response_body =
        std::str::from_utf8(response.body().context("Couldn't get response message")?)
            .context("Couldn't parse response message to string")?;
    Ok(response_body.to_string())
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let test_manager = TestManager::new(&opt.uri);
    test_manager
        .run_tests()
        .await
        .context("Couldn't run tests")?;

    Ok(())
}
