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

//! This is a minimal Rust client. It does a simple request, containing a string
// to an Oak application and expects a response with a string in it.
//

use log::info;
use minimal_client::proto::{minimal_client::MinimalClient, MinimalRequest};
use oak_abi::label::Label;
use prost::Message;
use structopt::StructOpt;
use tonic::{
    metadata::MetadataValue,
    transport::{Certificate, Channel, ClientTlsConfig},
    Request,
};

#[derive(StructOpt, Clone)]
#[structopt(about = "Minimal Client")]
pub struct Opt {
    #[structopt(
        long,
        help = "URI of the Oak application to connect to",
        default_value = "https://localhost:8080"
    )]
    uri: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS root certificate file used by gRPC client"
    )]
    root_tls_certificate: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    info!("Initialising and reading args");
    env_logger::init();
    let opt = Opt::from_args();

    let uri = opt.uri.parse().expect("Error parsing URI");
    let root_tls_certificate = tokio::fs::read(&opt.root_tls_certificate)
        .await
        .expect("Could not load certificate file");

    info!("Connecting to Oak Application: {:?}", uri);
    let tls_config =
        ClientTlsConfig::new().ca_certificate(Certificate::from_pem(root_tls_certificate));
    let channel = Channel::builder(uri)
        .tls_config(tls_config)
        .connect()
        .await
        .expect("Could not connect to Oak Application");

    // TODO(#1097): Turn the following logic into a proper reusable client library.
    info!("Generating public label");
    let mut label = Vec::new();
    Label::public_untrusted()
        .encode(&mut label)
        .expect("Error encoding label");

    info!("Creating client");
    let mut client = MinimalClient::with_interceptor(channel, move |mut request: Request<()>| {
        request.metadata_mut().insert_bin(
            oak_abi::OAK_LABEL_GRPC_METADATA_KEY,
            MetadataValue::from_bytes(label.as_ref()),
        );
        Ok(request)
    });

    let request = Request::new(MinimalRequest {
        request: String::from("Ferris"),
    });
    info!("Sending request: {:?}", request);

    let response = client
        .knock(request)
        .await
        .expect("Could not receive response");
    info!("Received response: {:?}", response);

    Ok(())
}
