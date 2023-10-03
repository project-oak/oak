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

use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use tokio::net::TcpListener;

const OAK_FUNCTIONS_CONTAINERS_APP_PORT: u16 = 8080;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let addr = SocketAddr::new(
        IpAddr::V4(Ipv4Addr::UNSPECIFIED),
        OAK_FUNCTIONS_CONTAINERS_APP_PORT,
    );
    let listener = TcpListener::bind(addr).await?;
    let server = tokio::spawn(oak_functions_containers_app::create(listener));
    println!(
        "Running Oak Functions on Oak Containers at port: {OAK_FUNCTIONS_CONTAINERS_APP_PORT}"
    );
    server.await??;

    Ok(())
}
