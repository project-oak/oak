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

//! Client for the Private Set Intersection example.

use anyhow::{anyhow, Context};
use http::uri::Uri;
use log::info;
use maplit::hashset;
use oak_abi::label::{confidentiality_label, web_assembly_module_signature_tag};
use oak_client::{
    create_tls_channel,
    interceptors::{auth::AuthInterceptor, label::LabelInterceptor, CombinedInterceptor},
};
use private_set_intersection_client::proto::{
    private_set_intersection_client::PrivateSetIntersectionClient, GetIntersectionRequest,
    SubmitSetRequest,
};
use std::collections::HashSet;
use structopt::StructOpt;
use tonic::{service::interceptor::InterceptedService, transport::Channel, Request};

#[derive(StructOpt, Clone)]
#[structopt(about = "Private Set Intersection Client")]
pub struct Opt {
    #[structopt(
        long,
        help = "URI of the Oak application to connect to",
        default_value = "https://localhost:8080"
    )]
    uri: String,
    #[structopt(long, help = "ID of the set intersection")]
    set_id: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS root certificate file used by gRPC client"
    )]
    root_tls_certificate: String,
    #[structopt(long, help = "Path to the PEM-encoded public key used as a data label")]
    public_key: String,
}

/// Create Oak gRPC client.
async fn create_client(
    uri: &Uri,
    root_tls_certificate: &[u8],
    public_key: &[u8],
) -> anyhow::Result<
    PrivateSetIntersectionClient<
        InterceptedService<Channel, CombinedInterceptor<AuthInterceptor, LabelInterceptor>>,
    >,
> {
    info!("Connecting to Oak Application: {:?}", uri);
    let channel = create_tls_channel(uri, root_tls_certificate)
        .await
        .context("Couldn't create TLS channel")?;
    let label = confidentiality_label(web_assembly_module_signature_tag(public_key));
    let key_pair = oak_sign::KeyPair::generate()?;
    let interceptor = oak_client::interceptors::combine(
        AuthInterceptor::create(key_pair),
        LabelInterceptor::create(&label).context("Couldn't create gRPC interceptor")?,
    );
    Ok(PrivateSetIntersectionClient::with_interceptor(
        channel,
        interceptor,
    ))
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let uri = opt.uri.parse().context("Error parsing URI")?;
    let root_tls_certificate =
        std::fs::read(&opt.root_tls_certificate).context("Couldn't load certificate file")?;
    let public_key_file =
        std::fs::read(&opt.public_key).context("Couldn't load public key file")?;
    let public_key_bytes = pem::parse(public_key_file)
        .context("Empty public key file")?
        .contents;

    // Submit sets from different clients.
    let mut client_1 = create_client(&uri, &root_tls_certificate, &public_key_bytes)
        .await
        .context("Couldn't create gRPC client")?;
    let request = Request::new(SubmitSetRequest {
        set_id: opt.set_id.to_string(),
        values: vec!["a".to_string(), "b".to_string(), "c".to_string()],
    });
    client_1
        .submit_set(request)
        .await
        .context("Couldn't submit set")?;

    let mut client_2 = create_client(&uri, &root_tls_certificate, &public_key_bytes)
        .await
        .context("Couldn't create gRPC client")?;
    let request = Request::new(SubmitSetRequest {
        set_id: opt.set_id.to_string(),
        values: vec!["b".to_string(), "c".to_string(), "d".to_string()],
    });
    client_2
        .submit_set(request)
        .await
        .context("Couldn't submit set")?;

    // Use an invalid public key.
    let invalid_public_key_bytes = base64::decode("vpxqTZOUq1FjcaB9uJYCuv4kAg+AsgMwubA6WE+2pmk=")
        .context("Couldn't decode public key")?;
    let mut invalid_client = create_client(&uri, &root_tls_certificate, &invalid_public_key_bytes)
        .await
        .context("Couldn't create gRPC client")?;

    let request = Request::new(SubmitSetRequest {
        set_id: opt.set_id.to_string(),
        values: vec!["c".to_string(), "d".to_string(), "e".to_string()],
    });
    invalid_client
        .submit_set(request)
        .await
        // Fail if set submission with an invalid key was successful.
        .err()
        .context("Submitted set with an invalid public key label")?;

    // Retrieve intersection.
    let expected_intersection = hashset!["b".to_string(), "c".to_string()];
    let response_1 = client_1
        .get_intersection(Request::new(GetIntersectionRequest {
            set_id: opt.set_id.to_string(),
        }))
        .await
        .context("Couldn't receive intersection")?;
    let intersection_1: HashSet<_> = response_1.get_ref().values.iter().cloned().collect();
    if expected_intersection != intersection_1 {
        return Err(anyhow!(
            "Incorrect client 1 intersection, expected {:?}, received {:?}",
            expected_intersection,
            intersection_1
        ));
    }
    info!("Client 1 intersection: {:?}", &intersection_1);

    let response_2 = client_2
        .get_intersection(Request::new(GetIntersectionRequest {
            set_id: opt.set_id.to_string(),
        }))
        .await
        .context("Couldn't receive intersection")?;
    let intersection_2: HashSet<_> = response_2.get_ref().values.iter().cloned().collect();
    if expected_intersection != intersection_2 {
        return Err(anyhow!(
            "Incorrect client 2 intersection, expected {:?}, received {:?}",
            expected_intersection,
            intersection_2
        ));
    }
    info!("Client 2 intersection: {:?}", &intersection_2);

    Ok(())
}
