//
// Copyright 2023 The Project Oak Authors
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

use clap::Parser;

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    let args = oak_containers_launcher::Args::parse();

    let mut untrusted_app = oak_containers_hello_world_untrusted_app::UntrustedApp::create(args)
        .await
        .map_err(|error| anyhow::anyhow!("couldn't create untrusted app: {}", error))?;

    let greeting = untrusted_app
        .hello("Untrusted App")
        .await
        .map_err(|error| anyhow::anyhow!("couldn't get greeting: {}", error))?;

    println!("Received a greeting from the trusted app: {:?}", greeting);

    Ok(())
}
