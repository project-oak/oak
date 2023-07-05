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

mod orchestrator_client;
mod untrusted_app_client;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let application_config = orchestrator_client::OrchestratorClient::create()
        .await?
        .get_application_config()
        .await?;
    let name = format!(
        "Trusted Application with a {} byte long config",
        application_config.len()
    );
    let mut untrusted_app_client =
        untrusted_app_client::UntrustedApplicationClient::create(2, 6969).await?;
    let _greeting = untrusted_app_client.hello(&name).await?;
    Ok(())
}
