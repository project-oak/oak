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

pub mod proto {
    tonic::include_proto!("oak.examples.trusted_information_retrieval");
}

use anyhow::anyhow;
use log::info;
use oak_abi::label::Label;
use prost::Message;
use proto::{
    trusted_information_retrieval_client::TrustedInformationRetrievalClient,
    ListPointsOfInterestRequest, Location,
};
use structopt::StructOpt;
use tonic::{
    metadata::MetadataValue,
    transport::{Certificate, Channel, ClientTlsConfig},
    Request,
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
        help = "PEM encoded X.509 TLS root certificate file used by gRPC client",
        default_value = ""
    )]
    grpc_client_root_tls_certificate: String,
    #[structopt(
        long,
        help = "Requested location (latitude and longitude separated by space)",
        default_value = ""
    )]
    location: Vec<f32>,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let uri = opt.uri.parse().expect("Error parsing URI");
    let root_certificate = tokio::fs::read(&opt.grpc_client_root_tls_certificate)
        .await
        .expect("Could load certificate file");
    if opt.location.len() != 2 {
        return Err(anyhow!(
            "Incorrect number of coordinates: {} (expected 2)",
            &opt.location.len()
        ));
    }
    let latitude = opt.location[0];
    let longitude = opt.location[1];

    info!("Connecting to Oak Application: {:?}", uri);
    let tls_config = ClientTlsConfig::new().ca_certificate(Certificate::from_pem(root_certificate));
    let channel = Channel::builder(uri)
        .tls_config(tls_config)
        .connect()
        .await
        .expect("Could not connect to Oak Application");

    let mut label = Vec::new();
    Label::public_untrusted()
        .encode(&mut label)
        .expect("Error encoding label");
    let mut client = TrustedInformationRetrievalClient::with_interceptor(
        channel,
        move |mut request: Request<()>| {
            request
                .metadata_mut()
                .insert_bin("x-oak-label-bin", MetadataValue::from_bytes(label.as_ref()));
            Ok(request)
        },
    );

    let request = Request::new(ListPointsOfInterestRequest {
        location: Some(Location {
            latitude,
            longitude,
        }),
    });
    info!("Sending request: {:?}", request);

    let response = client
        .list_points_of_interest(request)
        .await
        .expect("Could not receive response");
    info!("Received response: {:?}", response);

    Ok(())
}
