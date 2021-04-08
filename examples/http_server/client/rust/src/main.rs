//
// Copyright 2020 The Project Oak Authors
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

use anyhow::Result;
use oak_abi::label::{confidentiality_label, tls_endpoint_tag, Label};
use std::{fs, io};
use structopt::StructOpt;
#[derive(StructOpt, Clone)]
#[structopt(about = "HTTPS server pseudo-Node Client Example.")]
pub struct Opt {
    #[structopt(
        long,
        help = "Path to the PEM-encoded CA root certificate.",
        default_value = "../../certs/local/ca.pem"
    )]
    ca_cert_path: String,
}

#[tokio::main]
async fn main() -> Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let key_pair = oak_sign::KeyPair::generate()?;
    let signature =
        oak_sign::SignatureBundle::create(oak_abi::OAK_CHALLENGE.as_bytes(), &key_pair)?;

    // Signed challenge
    let signature = oak_abi::proto::oak::identity::SignedChallenge {
        signed_hash: signature.signed_hash,
        public_key: key_pair.public_key_der()?,
    };

    let path = &opt.ca_cert_path;
    let ca_file = fs::File::open(path).unwrap_or_else(|e| panic!("failed to open {}: {}", path, e));
    let mut ca = io::BufReader::new(ca_file);

    // Build an HTTP connector which supports HTTPS too.
    let mut http = hyper::client::HttpConnector::new();
    http.enforce_http(false);
    // Build a TLS client, using the custom CA store for lookups.
    let mut tls = rustls::ClientConfig::new();
    tls.root_store
        .add_pem_file(&mut ca)
        .expect("failed to load custom CA store");
    // Join the above part into an HTTPS connector.
    let https = hyper_rustls::HttpsConnector::from((http, tls));

    let client: hyper::client::Client<_, hyper::Body> =
        hyper::client::Client::builder().build(https);

    check_endpoint(
        &client,
        "https://localhost:8080",
        &Label::public_untrusted(),
        serde_json::to_string(&signature).unwrap(),
    )
    .await;

    check_endpoint(
        &client,
        "https://localhost:8081",
        &confidentiality_label(tls_endpoint_tag("localhost:8080")),
        serde_json::to_string(&signature).unwrap(),
    )
    .await;

    Ok(())
}

async fn check_endpoint(
    client: &hyper::client::Client<
        hyper_rustls::HttpsConnector<hyper::client::HttpConnector>,
        hyper::Body,
    >,
    uri: &str,
    label: &Label,
    signature: String,
) {
    let label_bytes = serde_json::to_string(label)
        .expect("Could not serialize public/untrusted label to JSON.")
        .into_bytes();

    let request = hyper::Request::builder()
        .method(http::Method::GET)
        .uri(uri)
        .header(oak_abi::OAK_LABEL_HTTP_JSON_KEY, label_bytes)
        .header(oak_abi::OAK_SIGNED_CHALLENGE_HTTP_JSON_KEY, signature)
        .body(hyper::Body::empty())
        .unwrap();

    let resp = client
        .request(request)
        .await
        .expect("Error while awaiting response");

    assert_eq!(resp.status(), http::StatusCode::OK);

    log::info!("response: {:?}", resp);
    log::info!(
        "response body: {:?}",
        hyper::body::to_bytes(resp.into_body())
            .await
            .expect("could not read response body")
    );
}
