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
//

#![feature(never_type)]
#![feature(result_flattening)]
#![feature(array_chunks)]

use clap::Parser;
use oak_launcher_utils::launcher;
use quirk_echo_launcher::proto::quirk::echo::{EchoAsyncClient, EchoRequest};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = crate::launcher::Params::parse();
    env_logger::init();

    log::info!("calling launcher");
    let (guest_instance, connector_handle) = launcher::launch(cli).await?;

    let mut client = EchoAsyncClient::new(connector_handle);
    let body = b"test_msg".to_vec();
    let echo_request = EchoRequest { body: body.clone() };

    log::info!("invoking remote method");
    let echo_response = client
        .echo(&echo_request)
        .await
        .expect("Failed to receive response.");

    assert!(echo_response.is_ok());
    assert_eq!(body, echo_response.unwrap().body);

    log::info!("killing instance");
    guest_instance
        .kill()
        .await
        .expect("Failed to stop launcher");

    Ok(())
}
