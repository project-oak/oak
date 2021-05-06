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
use log::info;
use oak_functions_abi::proto::{Response, StatusCode};
use oak_functions_abitest_common::*;
use prost::Message;
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
        info!("{} test is successful", test_name);
        Ok(())
    }
}

async fn send_request(uri: &str, body: &str) -> anyhow::Result<String> {
    let http = hyper::client::HttpConnector::new();
    let client: hyper::client::Client<_, hyper::Body> = hyper::client::Client::builder()
        .http2_only(true)
        .build(http);

    let request = hyper::Request::builder()
        .method(http::Method::POST)
        .uri(uri)
        .body(body.to_string().into())
        .context("Couldn't create HTTP request")?;

    let response = client
        .request(request)
        .await
        .context("Couldn't send request")?;
    assert_eq!(response.status(), http::StatusCode::OK);

    let body = hyper::body::to_bytes(response.into_body())
        .await
        .context("Couldn't read response body")?;
    let result = Response::decode(body).context("Couldn't decode response body")?;
    assert_eq!(StatusCode::Success as i32, result.status);

    let message = String::from_utf8(
        result
            .body()
            .context("Couldn't get response message")?
            .to_vec(),
    )
    .context("Couldn't parse response message to string")?;
    Ok(message)
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
