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

use anyhow::Context;
use log::info;
use oak_abi::label::Label;
use oak_client::{create_tls_channel, interceptors::label::LabelInterceptor};
use structopt::StructOpt;
use tonic::Request;
use treehouse_client::proto::{treehouse_client::TreehouseClient, GetCardsRequest};

#[derive(StructOpt, Clone)]
#[structopt(about = "Treehouse Client")]
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
    #[structopt(long, help = "Search calendar events on a specified date")]
    date: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let uri = opt.uri.parse().context("Error parsing URI")?;
    let root_tls_certificate =
        std::fs::read(&opt.root_tls_certificate).context("Couldn't load certificate file")?;
    let date = opt.date;

    info!("Connecting to Oak Application: {:?}", uri);
    let channel = create_tls_channel(&uri, &root_tls_certificate)
        .await
        .context("Couldn't create TLS channel")?;
    let label = Label::public_untrusted();
    let interceptor =
        LabelInterceptor::create(&label).context("Couldn't create gRPC interceptor")?;
    let mut client = TreehouseClient::with_interceptor(channel, interceptor);

    let request = Request::new(GetCardsRequest { date });
    info!("Sending request: {:?}", request);

    let response = client
        .get_cards(request)
        .await
        .context("Couldn't receive response")?;
    info!("Received response: {:?}", response);

    Ok(())
}
