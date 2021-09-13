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

use futures_util::stream::iter;
use http::Uri;
use log::info;
use proto::{hello_world_client::HelloWorldClient, HelloRequest};
use std::time::Duration;
use structopt::StructOpt;
use tokio::{sync::mpsc, time};
use tonic::transport::{Channel, ClientTlsConfig};

pub mod proto {
    tonic::include_proto!("oak.examples.hello_world");
}

#[derive(StructOpt, Clone)]
#[structopt(about = "Streaming gRPC test")]
pub struct Opt {
    #[structopt(
        long,
        help = "URI of the gRPC server to connect to",
        default_value = "http://localhost:8080"
    )]
    uri: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let opt = Opt::from_args();

    let uri: Uri = opt.uri.parse()?;
    let use_tls = uri.scheme_str() == Some("https");

    let mut endpoint = Channel::builder(uri);
    if use_tls {
        endpoint = endpoint.tls_config(ClientTlsConfig::new())?;
    }

    let channel = endpoint.connect().await?;
    let mut client = HelloWorldClient::new(channel);

    test_unary(&mut client).await?;
    test_client_streaming(&mut client).await?;
    test_server_streaming(&mut client).await?;
    test_bidi_streaming(&mut client).await?;

    Ok(())
}

async fn test_unary(
    client: &mut HelloWorldClient<Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Testing unary request");

    let request = tonic::Request::new(HelloRequest {
        greeting: "World".into(),
    });

    let response = client.say_hello(request).await?;

    info!("reply={:?}", response.into_inner().reply);

    Ok(())
}

async fn test_client_streaming(
    client: &mut HelloWorldClient<Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Testing client streaming");

    let requests = vec![
        HelloRequest {
            greeting: "A".into(),
        },
        HelloRequest {
            greeting: "B".into(),
        },
    ];

    let request = tonic::Request::new(iter(requests));

    let response = client.lots_of_greetings(request).await?;

    info!("reply={:?}", response.into_inner().reply);

    Ok(())
}

async fn test_server_streaming(
    client: &mut HelloWorldClient<Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Testing server streaming");

    let request = tonic::Request::new(HelloRequest {
        greeting: "World".into(),
    });

    let mut stream = client.lots_of_replies(request).await?.into_inner();

    while let Some(response) = stream.message().await? {
        info!("reply={:?}", response.reply);
    }

    Ok(())
}

async fn test_bidi_streaming(
    client: &mut HelloWorldClient<Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Testing bidirectional streaming");

    let (sender, mut receiver) = mpsc::channel(4);

    let outbound = async_stream::stream! {
        let mut interval = time::interval(Duration::from_secs(1));
        interval.tick().await;
        yield HelloRequest {
            greeting: "A".into(),
        };
        receiver.recv().await.unwrap();
        interval.tick().await;
        yield HelloRequest {
            greeting: "B".into(),
        };
        receiver.recv().await.unwrap();
        interval.tick().await;
        yield HelloRequest {
            greeting: "C".into(),
        };
        receiver.recv().await.unwrap();
    };

    let response = client.bidi_hello(tonic::Request::new(outbound)).await?;

    let mut inbound = response.into_inner();

    while let Some(response) = inbound.message().await? {
        sender.send(()).await?;
        info!("reply={:?}", response.reply);
    }

    Ok(())
}
