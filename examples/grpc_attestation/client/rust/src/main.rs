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

use anyhow::{anyhow, Context};
use log::info;
use oak_grpc_attestation_client::AttestationClient;
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
#[structopt(about = "Proxy Attestation Client")]
pub struct Opt {
    #[structopt(
        long,
        help = "URI of the gRPC Attestation Service",
        default_value = "http://localhost:8080"
    )]
    uri: String,
}

// TODO(#1867): Add remote attestation support.
const TEST_TEE_MEASUREMENT: &str = "Test TEE measurement";
const INVALID_TEST_TEE_MEASUREMENT: &str = "Invalid test TEE measurement";
// Example message expected from the Oak application.
const EXAMPLE_MESSAGE: &str = "Example message";

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    if AttestationClient::create(&opt.uri, INVALID_TEST_TEE_MEASUREMENT.as_bytes())
        .await
        .is_ok()
    {
        return Err(anyhow!("Invalid TEE measurement accepted"));
    }

    info!("Creating client");
    let mut client = AttestationClient::create(&opt.uri, TEST_TEE_MEASUREMENT.as_bytes())
        .await
        .context("Couldn't create client")?;

    info!("Sending request");
    let response = client
        .send(EXAMPLE_MESSAGE.as_bytes())
        .await
        .context("Couldn't send message")?
        .context("No message received")?;
    let data = String::from_utf8(response).context("Couldn't parse response")?;
    info!("Client received data: {:?}", data);

    Ok(())
}
