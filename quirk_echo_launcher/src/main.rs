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

mod channel;
mod launcher;
mod schema;

#[derive(Parser, Debug)]
struct Args {
    /// Execution mode.
    #[command(subcommand)]
    mode: crate::launcher::GuestMode,

    /// Port to listen on.
    #[arg(long, default_value = "8080")]
    port: u16,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Args::parse();
    env_logger::init();

    let (guest_instance, connector_handle) = crate::launcher::launch(cli.mode).await?;

    let mut client = schema::EchoAsyncClient::new(connector_handle);
    let body = b"test_msg".to_vec();
    let echo_request = schema::EchoRequest { body: body.clone() };

    let echo_response = client
        .echo(&echo_request)
        .await
        .expect("Failed to receive response.");

    assert!(echo_response.is_ok());
    assert_eq!(body, echo_response.unwrap().body);

    guest_instance
        .kill()
        .await
        .expect("Failed to stop launcher");

    Ok(())
}
