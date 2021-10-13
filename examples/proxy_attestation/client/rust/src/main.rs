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

//! Client for the Proxy Attestation example.
//!
//! Client first connects to the Proxy Attestation Service and downloads its root certificate.
//! Then client uses this certificate in order to connect to the example Oak application, assuming
//! that the example application received a signed certificate from the Proxy Attestation Service.

use anyhow::Context;
use assert_matches::assert_matches;
use http::uri::Uri;
use log::info;
use oak_abi::label::Label;
use oak_client::{
    attestation::create_attested_grpc_channel, create_tls_channel,
    interceptors::label::LabelInterceptor,
};
use oak_proxy_attestation::proto::{
    proxy_attestation_client::ProxyAttestationClient, GetRootCertificateRequest,
};
use proxy_attestation_client::proto::{
    example_application_client::ExampleApplicationClient, GetExampleMessageRequest,
};
use structopt::StructOpt;
use tonic::{service::interceptor::InterceptedService, transport::Channel, Request};

#[derive(StructOpt, Clone)]
#[structopt(about = "Proxy Attestation Client")]
pub struct Opt {
    #[structopt(
        long,
        help = "URI of the Oak application",
        default_value = "https://localhost:8080"
    )]
    app_uri: String,
    #[structopt(
        long,
        help = "URI of the Proxy Attestation Service",
        default_value = "https://localhost:8888"
    )]
    proxy_uri: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS root certificate file of Proxy Attestation Service"
    )]
    proxy_root_tls_certificate: String,
}

// TODO(#1867): Add remote attestation support.
const TEST_TEE_MEASUREMENT: &str = "Test TEE measurement";
const INVALID_TEST_TEE_MEASUREMENT: &str = "Invalid test TEE measurement";
// Example message expected from the Oak application.
const EXAMPLE_MESSAGE: &str = "Example message";

/// Create gRPC client for Proxy Attestation Service.
async fn create_proxy_client(
    uri: &Uri,
    root_tls_certificate: &[u8],
) -> anyhow::Result<ProxyAttestationClient<Channel>> {
    info!("Connecting to Proxy Attestation Service: {:?}", uri);
    let channel = create_tls_channel(uri, root_tls_certificate)
        .await
        .context("Couldn't create TLS channel")?;
    Ok(ProxyAttestationClient::new(channel))
}

/// Create gRPC client for Oak application.
async fn create_application_client(
    uri: &Uri,
    root_tls_certificate: &[u8],
    tee_measurement: &[u8],
) -> anyhow::Result<ExampleApplicationClient<InterceptedService<Channel, LabelInterceptor>>> {
    info!("Connecting to Oak application: {:?}", uri);
    let channel = create_attested_grpc_channel(uri, root_tls_certificate, tee_measurement)
        .await
        .context("Couldn't create TLS channel")?;
    let label = Label::public_untrusted();
    let interceptor =
        LabelInterceptor::create(&label).context("Couldn't create gRPC interceptor")?;
    Ok(ExampleApplicationClient::with_interceptor(
        channel,
        interceptor,
    ))
}

/// Request root TLS certificate from Proxy Attestation Service.
async fn get_root_tls_certificate(
    proxy_uri: &Uri,
    proxy_root_tls_certificate: &[u8],
) -> anyhow::Result<Vec<u8>> {
    let mut client = create_proxy_client(proxy_uri, proxy_root_tls_certificate)
        .await
        .context("Couldn't create gRPC client")?;
    let request = Request::new(GetRootCertificateRequest {});
    let response = client
        .get_root_certificate(request)
        .await
        .context("Couldn't get public key")?;
    Ok(response.get_ref().root_certificate.to_vec())
}

/// Connect to Oak application using root TLS certificate received from Proxy Attestation Service.
async fn get_example_message(
    uri: &Uri,
    root_tls_certificate: &[u8],
    tee_measurement: &[u8],
) -> anyhow::Result<String> {
    let mut client = create_application_client(uri, root_tls_certificate, tee_measurement)
        .await
        .context("Couldn't create gRPC client")?;
    let request = Request::new(GetExampleMessageRequest {});
    let example_message = client
        .get_example_message(request)
        .await
        .context("Couldn't connect to backend")?
        .into_inner()
        .message;
    Ok(example_message)
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let app_uri = opt.app_uri.parse().context("Error parsing URI")?;
    let proxy_uri = opt.proxy_uri.parse().context("Error parsing URI")?;
    let proxy_root_tls_certificate =
        std::fs::read(&opt.proxy_root_tls_certificate).context("Couldn't load certificate file")?;

    let root_tls_certificate =
        get_root_tls_certificate(&proxy_uri, &proxy_root_tls_certificate).await?;
    info!("Received root certificate from Proxy Attestation Service");

    // Test that invalid TEE measurements are not accepted by the client.
    let result = get_example_message(
        &app_uri,
        &root_tls_certificate,
        INVALID_TEST_TEE_MEASUREMENT.as_bytes(),
    )
    .await;
    assert_matches!(result, Err(_));

    let example_message = get_example_message(
        &app_uri,
        &root_tls_certificate,
        TEST_TEE_MEASUREMENT.as_bytes(),
    )
    .await
    .context("Couldn't send request")?;
    assert_eq!(EXAMPLE_MESSAGE, example_message);
    info!("Successfully connected to: {:?}", &opt.proxy_uri);

    Ok(())
}
