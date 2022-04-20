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
use std::net::{Ipv6Addr, SocketAddr};
use warp::Filter;

#[derive(Parser, Clone, Debug)]
pub struct Opt {
    #[clap(long, default_value = "8080", help = "Port number on which to listen.")]
    port: u16,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::parse();
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, opt.port));

    let encrypted_echo = warp::post()
        .and(warp::path("encrypted_echo"))
        // Only accept bodies smaller than 16kb...
        .and(warp::body::content_length_limit(1024 * 16))
        .and(warp::body::bytes())
        .map(|body: bytes::Bytes| warp::reply::Response::new(body.into()));

    warp::serve(encrypted_echo).run(address).await;
    Ok(())
}
