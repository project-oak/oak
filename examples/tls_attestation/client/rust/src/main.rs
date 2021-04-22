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

//! Client for the TLS Attestation example.

use anyhow::Context;
use assert_matches::assert_matches;
use log::info;
use oak_abi::label::Label;
use oak_client::attestation::create_attested_https_client;
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
#[structopt(about = "TLS Attestation Client")]
pub struct Opt {
    #[structopt(
        long,
        help = "URI of the TLS Attestation Service",
        default_value = "https://localhost:8888"
    )]
    proxy_uri: String,
}

// TODO(#1867): Add remote attestation support.
const TEST_TEE_MEASUREMENT: &str = "Test TEE measurement";
const INVALID_TEST_TEE_MEASUREMENT: &str = "Invalid test TEE measurement";
// Example message expected from the Oak application.
const EXAMPLE_MESSAGE: &str = "Example message";

/// Connect to the TEE application via HTTPS using the attested TLS channel.
async fn send_request(
    client: &hyper::client::Client<
        hyper_rustls::HttpsConnector<hyper::client::HttpConnector>,
        hyper::Body,
    >,
    uri: &str,
) -> anyhow::Result<String> {
    let label = Label::public_untrusted();
    let label_bytes = serde_json::to_string(&label)
        .expect("Couldn't serialize label to JSON")
        .into_bytes();

    let request = hyper::Request::builder()
        .method(http::Method::GET)
        .uri(uri)
        .header(oak_abi::OAK_LABEL_HTTP_JSON_KEY, label_bytes)
        .body(hyper::Body::empty())
        .context("Couldn't create request")?;

    let response = client
        .request(request)
        .await
        .context("Couldn't send request")?;
    assert_eq!(response.status(), http::StatusCode::OK);
    info!("Response: {:?}", response);

    let response_body = String::from_utf8(
        hyper::body::to_bytes(response.into_body())
            .await
            .context("Couldn't read response body")?
            .to_vec(),
    )
    .context("Couldn't decode response body")?;

    info!("Response body: {:?}", response_body);
    Ok(response_body)
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    // Test that invalid TEE measurements are not accepted by the client.
    let invalid_client = create_attested_https_client(INVALID_TEST_TEE_MEASUREMENT.as_bytes())
        .await
        .context("Couldn't create HTTPS client")?;
    let result = send_request(&invalid_client, &opt.proxy_uri).await;
    assert_matches!(result, Err(_));

    let client = create_attested_https_client(TEST_TEE_MEASUREMENT.as_bytes())
        .await
        .context("Couldn't create HTTPS client")?;
    let example_message = send_request(&client, &opt.proxy_uri)
        .await
        .context("Couldn't send request")?;
    assert_eq!(EXAMPLE_MESSAGE, example_message);
    info!("Successfully connected to: {:?}", &opt.proxy_uri);

    Ok(())
}
