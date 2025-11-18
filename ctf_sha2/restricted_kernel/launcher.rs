//
// Copyright 2025 The Project Oak Authors
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

#![feature(never_type)]
#![feature(result_flattening)]

use clap::Parser;
use oak_launcher_utils::launcher;
use service::oak::ctf_sha2::enclave::{FlagDigestServiceAsyncClient, GenerateFlagDigestRequest};

#[derive(Parser, Debug)]
pub struct Args {
    #[clap(flatten)]
    launcher_params: oak_launcher_utils::launcher::Params,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();

    let cli = Args::parse();
    let (guest_instance, connector_handle) = launcher::launch(cli.launcher_params).await?;

    let result = FlagDigestServiceAsyncClient::new(connector_handle)
        .generate_flag_digest(&GenerateFlagDigestRequest {})
        .await
        .flatten()?;

    // TODO: b/436216021 - save the result to some .binpb file.
    println!("{:?}", result);

    guest_instance.kill().await?;
    Ok(())
}
