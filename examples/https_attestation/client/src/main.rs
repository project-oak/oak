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

//! Client for the HTTPS Attestation example.
//!
//! Performs remote attestation via sending an HTTP POST request to `proxy_uri/report` and verifying
//! assertions from the response.

use anyhow::Context;
use log::info;
use oak_attestation_common::keying_material::Assertion;
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
#[structopt(about = "HTTPS Attestation Client")]
pub struct Opt {
    #[structopt(
        long,
        help = "PEM encoded X.509 root TLS certificate file required for connecting to the HTTPS Attestation Service.",
        default_value = "./examples/certs/local/ca.pem"
    )]
    root_https_certificate: String,
    #[structopt(
        long,
        help = "URI of the HTTPS Attestation Service",
        default_value = "https://localhost:8888"
    )]
    attestation_service_uri: String,
}

// Example message expected from the server.
const EXAMPLE_MESSAGE: &str = "Example message";

async fn send_request(
    client: &hyper::client::Client<
        hyper_rustls::HttpsConnector<hyper::client::HttpConnector>,
        hyper::Body,
    >,
    uri: &str,
    method: http::Method,
) -> anyhow::Result<String> {
    let request = hyper::Request::builder()
        .method(method)
        .uri(uri)
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
    Ok(response_body)
}

fn verify_server_assertion(serialized_assertion: &str) -> anyhow::Result<()> {
    Assertion::from_string(serialized_assertion)
        .context("Couldn't deserialize server assertion")?;
    // TODO(#2048): Implement client assertion generation.
    Ok(())
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let path = &opt.root_https_certificate;
    let ca_file =
        std::fs::File::open(path).unwrap_or_else(|e| panic!("Couldn't open {}: {}", path, e));
    let mut ca = std::io::BufReader::new(ca_file);

    // Build an HTTP connector which supports HTTPS too.
    let mut http_connector = hyper::client::HttpConnector::new();
    http_connector.enforce_http(false);
    // Build a TLS client, using the custom CA store for lookups.
    let mut tls_config = rustls::ClientConfig::new();
    tls_config
        .root_store
        .add_pem_file(&mut ca)
        .expect("Couldn't load custom CA store");
    // Join the above part into an HTTPS connector.
    let https_connector = hyper_rustls::HttpsConnector::from((http_connector, tls_config));

    let client: hyper::client::Client<_, hyper::Body> =
        hyper::client::Client::builder().build(https_connector);

    // Send remote attestation request via HTTP POST message.
    // `/report` is used to connect to the HTTPS Attestation Service directly.
    let assertion_url = format!("{}/report", &opt.attestation_service_uri);
    info!("Connecting to: {:?}", &assertion_url);
    let assertion = send_request(&client, &assertion_url, http::Method::POST)
        .await
        .context("Couldn't send request")?;
    verify_server_assertion(&assertion).context("Incorrect server assertion")?;

    // Request an example message from the backend server.
    // `/invoke` is used to tell HTTPS Attestation Service to proxy the request to the backend
    // server.
    let application_url = format!("{}/invoke", &opt.attestation_service_uri);
    info!("Connecting to: {:?}", &application_url);
    let example_message = send_request(&client, &application_url, http::Method::GET)
        .await
        .context("Couldn't send request")?;
    info!("Example message: {:?}", &example_message);
    assert_eq!(EXAMPLE_MESSAGE, example_message);

    Ok(())
}
