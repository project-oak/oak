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

use log::info;
use proto::hello_world_client::HelloWorldClient;
use proto::HelloRequest;
use tonic::transport::{Certificate, Channel, ClientTlsConfig};

pub mod proto {
    tonic::include_proto!("oak.examples.hello_world");
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let root_cert = tokio::fs::read("examples/certs/ca.pem").await?;
    let root_cert = Certificate::from_pem(root_cert);
    let tls_config = ClientTlsConfig::new()
        .ca_certificate(root_cert)
        .domain_name("project-oak.local");

    let channel = Channel::from_static("https://[::1]:50051")
        .tls_config(tls_config)
        .connect()
        .await?;

    let mut client = HelloWorldClient::new(channel);

    let request = tonic::Request::new(HelloRequest {
        greeting: "World".into(),
    });

    let response = client.say_hello(request).await?;

    info!("RESPONSE={:?}", response);

    Ok(())
}
