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

//! Client for the Trusted Information Retrieval example.

use anyhow::Context;
use log::info;
use oak_abi::label::Label;
use oak_client::{create_tls_channel, Interceptor};
use structopt::StructOpt;
use tonic::Request;
use trusted_information_retrieval_client::proto::{
    trusted_information_retrieval_client::TrustedInformationRetrievalClient,
    GetPointOfInterestRequest,
};

#[derive(StructOpt, Clone)]
#[structopt(about = "Trusted Information Retrieval Client")]
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
    #[structopt(long, help = "ID of the point of interest")]
    id: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let uri = opt.uri.parse().context("Error parsing URI")?;
    let root_tls_certificate = tokio::fs::read(&opt.root_tls_certificate)
        .await
        .context("Could not load certificate file")?;
    let id = opt.id;

    info!("Connecting to Oak Application: {:?}", uri);
    let channel = create_tls_channel(&uri, &root_tls_certificate)
        .await
        .context("Couldn't create TLS channel")?;
    let label = Label::public_untrusted();
    let interceptor = Interceptor::create(&label).context("Couldn't create gRPC interceptor")?;
    let mut client = TrustedInformationRetrievalClient::with_interceptor(channel, interceptor);

    let request = Request::new(GetPointOfInterestRequest { id });
    info!("Sending request: {:?}", request);

    let response = client
        .get_point_of_interest(request)
        .await
        .expect("Could not receive response");
    info!("Received response: {:?}", response);

    Ok(())
}
