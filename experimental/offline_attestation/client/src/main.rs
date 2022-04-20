//
// Copyright 2022 The Project Oak Authors
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

use clap::Parser;
use log::info;
use url::Url;

const ECHO_PATH: &str = "encrypted_echo";

#[derive(Parser, Clone)]
#[clap(about = "Offline Attestation Client")]
pub struct Opt {
    #[clap(
        long,
        help = "URL of the server",
        default_value = "http://localhost:8080"
    )]
    url: String,
    #[clap(
        long,
        help = "The message to send to the server",
        default_value = "test"
    )]
    message: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::parse();
    let base = Url::parse(&opt.url)?;
    let echo = base.join(ECHO_PATH)?;
    let body = opt.message.as_bytes().to_vec();

    let response = reqwest::Client::new().post(echo).body(body).send().await?;
    let result = String::from_utf8(response.bytes().await?.to_vec())?;
    info!("Result: {}", result);
    Ok(())
}
