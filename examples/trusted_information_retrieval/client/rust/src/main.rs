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
        help = "PEM encoded X.509 TLS root certificate file used by gRPC client"
    )]
    grpc_client_root_tls_certificate: String,
    #[structopt(long, help = "Requested location's latitude (WGS84)")]
    latitude: f32,
    #[structopt(long, help = "Requested location's longitude (WGS84)")]
    longitude: f32,
}

// Metadata key that is used for storing Oak labels in the gRPC request.
// https://github.com/grpc/grpc/blob/master/doc/PROTOCOL-HTTP2.md.
const OAK_LABEL_GRPC_METADATA_KEY: &str = "x-oak-label-bin";

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let opt = Opt::from_args();

    let uri = opt.uri.parse().expect("Error parsing URI");
    let root_certificate = tokio::fs::read(&opt.grpc_client_root_tls_certificate)
        .await
        .expect("Could not load certificate file");
    let latitude = opt.latitude;
    if opt.latitude < -90.0 || opt.latitude > 90.0 {
        panic!(
            "Latitude must be a valid floating point number >=-90 and <= 90, found {}",
            latitude
        );
    }
    let longitude = opt.longitude;
    if opt.longitude < -180.0 || opt.longitude > 180.0 {
        panic!(
            "Longitude must be a valid floating point number >= -180 and <= 180, found {}",
            longitude
        );
    }

    info!("Connecting to Oak Application: {:?}", uri);
    let tls_config = ClientTlsConfig::new().ca_certificate(Certificate::from_pem(root_certificate));
    let channel = Channel::builder(uri)
        .tls_config(tls_config)
        .connect()
        .await
        .expect("Could not connect to Oak Application");

    // TODO(#1097): Turn the following logic into a proper reusable client library.
    let mut label = Vec::new();
    Label::public_untrusted()
        .encode(&mut label)
        .expect("Error encoding label");
    let mut client = TrustedInformationRetrievalClient::with_interceptor(
        channel,
        move |mut request: Request<()>| {
            request.metadata_mut().insert_bin(
                OAK_LABEL_GRPC_METADATA_KEY,
                MetadataValue::from_bytes(label.as_ref()),
            );
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
