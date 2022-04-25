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

use std::io::{stdin, BufRead};

use clap::Parser;
use tonic::Request;

pub mod proto {
    tonic::include_proto!("oak.session.unary.v1");
}

use proto::{unary_session_client::UnarySessionClient, UnaryRequest};

const MOCK_SESSION_ID: [u8; 8] = [0; 8];

#[derive(Parser, Debug)]
struct Args {
    /// address of the server
    #[clap(long, default_value = "http://127.0.0.1:8000")]
    server: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Args::parse();

    let mut client = UnarySessionClient::connect(cli.server).await?;

    for line in stdin().lock().lines() {
        let request = Request::new(UnaryRequest {
            body: line.unwrap().as_bytes().to_vec(),
            session_id: MOCK_SESSION_ID.to_vec(),
        });
        let response = client.message(request).await?;
        println!(
            "Response: {:?}",
            core::str::from_utf8(&response.into_inner().body)
        );
    }

    println!("Hello, world!");
    Ok(())
}
