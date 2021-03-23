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

//! Client for the Trusted Database example.

use anyhow::{ensure, Context};
use log::info;
use oak_abi::label::{confidentiality_label, public_key_identity_tag};
use oak_client::{
    create_tls_channel,
    interceptors::{auth::AuthInterceptor, combine, label::LabelInterceptor},
};
use structopt::StructOpt;
use tonic::Request;
use trusted_database_client::proto::{
    trusted_database_client::TrustedDatabaseClient, ListPointsOfInterestRequest, Location,
};

#[derive(StructOpt, Clone)]
#[structopt(about = "Trusted Database Client")]
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
    #[structopt(long, help = "Requested location's latitude in degrees (WGS84)")]
    latitude: f32,
    #[structopt(long, help = "Requested location's longitude in degrees (WGS84)")]
    longitude: f32,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let uri = opt.uri.parse().context("Error parsing URI")?;
    let root_tls_certificate =
        std::fs::read(&opt.root_tls_certificate).context("Couldn't load certificate file")?;
    let latitude = opt.latitude;
    ensure!(
        latitude >= -90.0 && latitude <= 90.0,
        "Latitude must be a valid floating point number >=-90 and <= 90, found {}",
        latitude
    );
    let longitude = opt.longitude;
    ensure!(
        longitude >= -180.0 && longitude <= 180.0,
        "Longitude must be a valid floating point number >= -180 and <= 180, found {}",
        longitude
    );

    info!("Connecting to Oak Application: {:?}", uri);
    let channel = create_tls_channel(&uri, &root_tls_certificate)
        .await
        .context("Couldn't create TLS channel")?;

    let key_pair = oak_sign::KeyPair::generate()?;
    let label = confidentiality_label(public_key_identity_tag(&key_pair.public_key_der()?));
    let label_interceptor =
        LabelInterceptor::create(&label).context("Couldn't create gRPC interceptor")?;
    let auth_interceptor = AuthInterceptor::create(key_pair);

    let interceptor = combine(label_interceptor, auth_interceptor);
    let mut client = TrustedDatabaseClient::with_interceptor(channel, interceptor);

    let request = Request::new(ListPointsOfInterestRequest {
        location: Some(Location {
            latitude_degrees: latitude,
            longitude_degrees: longitude,
        }),
    });
    info!("Sending request: {:?}", request);

    let response = client
        .list_points_of_interest(request)
        .await
        .context("Couldn't receive response")?;
    info!("Received response: {:?}", response);

    Ok(())
}
