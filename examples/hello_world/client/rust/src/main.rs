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

//! Hello World client that sends simple requests to the server and prints
//! the responses that it receives back.

#![feature(async_closure)]

use anyhow::Context;
use hello_world_grpc::proto::{hello_world_client::HelloWorldClient, HelloRequest};
use log::info;
use oak_abi::label::Label;
use oak_client::{create_tls_channel, interceptors::label::LabelInterceptor};
use structopt::StructOpt;
use tonic::Request;
#[derive(StructOpt, Clone)]
#[structopt(about = "Hello World Client")]
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
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    info!("Initialising and reading args");
    let opt = Opt::from_args();

    let uri = opt.uri.parse().context("Error parsing URI")?;
    let root_tls_certificate =
        std::fs::read(&opt.root_tls_certificate).context("Could not load certificate file")?;

    info!("Connecting to Oak Application: {:?}", uri);
    let channel = create_tls_channel(&uri, &root_tls_certificate)
        .await
        .context("Couldn't create TLS channel")?;
    let label = Label::public_untrusted();
    let interceptor =
        LabelInterceptor::create(&label).context("Couldn't create gRPC interceptor")?;
    let client = HelloWorldClient::with_interceptor(channel, interceptor);

    let worlds = vec!["WORLD", "MONDO", "世界", "MONDE"];
    info!("Sending requests");
    let responses = worlds
        .iter()
        .map(|world| {
            let req = Request::new(HelloRequest {
                greeting: String::from(*world),
            });
            // https://docs.rs/tonic/0.3.0/tonic/client/index.html#concurrent-usage
            let mut c = client.clone();
            async move {
                // Process each request concurrently.
                let result = c.say_hello(req).await;
                match result {
                    Ok(res) => {
                        info!("Received response: {}", res.get_ref().reply);
                        res.get_ref().reply.clone()
                    }
                    Err(e) => panic!("Error sending request {:?}", e),
                }
            }
        })
        .collect::<Vec<_>>();

    // Join all the tasks. NB: this is where the tasks are being run!
    futures::future::join_all(responses).await;

    Ok(())
}
