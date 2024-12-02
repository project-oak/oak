//
// Copyright 2024 The Project Oak Authors
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

//! Sends a string to the enclave app and prints the return.

use anyhow::Context;
use clap::Parser;

#[derive(Parser, Clone)]
#[command(about = "Oak Echo Client")]
pub struct Opt {
    #[arg(
        long,
        help = "URI of the Echo enclave application to connect to",
        default_value = "http://localhost:8080"
    )]
    uri: String,

    #[arg(long, help = "The message to send to the enclave application")]
    request: Option<String>,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::parse();

    let mut client = oak_gcp_examples_echo_client::EchoClient::create(&opt.uri)
        .await
        .context("couldn't connect to server")?;

    if let Some(request) = opt.request {
        println!("Request: {request}");
        let decrypted_response = String::from_utf8(
            client.echo(request.as_bytes()).await.context("couldn't send request")?,
        )
        .context("response is not valid UTF-8")?;
        println!("Response: {decrypted_response}");
    } else {
        for line in std::io::stdin().lines() {
            let decrypted_response = String::from_utf8(
                client
                    .echo(line.context("invalid line")?.as_bytes())
                    .await
                    .context("couldn't send request")?,
            )
            .context("response is not valid UTF-8")?;
            println!("{decrypted_response}");
        }
    }

    Ok(())
}
