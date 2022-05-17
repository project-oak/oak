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

//! Trusted Shuffler server.

mod http;

use crate::http::ServiceBuilder;
use anyhow::Context;
use clap::Parser;
use futures_util::FutureExt;
use hyper::Server;
use log::info;
use tokio::time::Duration;

#[derive(Parser, Clone)]
#[clap(about = "Trusted Shuffler Server")]
pub struct Opt {
    #[structopt(long, help = "Anonymity value", default_value = "1")]
    k: usize,
    #[structopt(
        long,
        help = "Address to listen on for the Trusted Shuffler server",
        default_value = "[::]:8888"
    )]
    listen_address: String,
    #[structopt(
        long,
        help = "URL of the backend to connect to from the Trusted Shuffler server",
        default_value = "http://localhost:8080"
    )]
    backend_url: String,
    #[structopt(
        long,
        help = "Timeout for the backend after the server received k requests in milliseconds.",
        default_value = "0"
    )]
    // TODO(mschett): Can we change this to Duration? Problem seems to be FromStr not satisfied.
    timeout: u64,
}

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    env_logger::builder()
        .format_timestamp(None)
        .format_level(false)
        .format_module_path(false)
        .format_target(false)
        .init();
    let opt = Opt::parse();

    let listen_address = opt
        .listen_address
        .parse()
        .context("Couldn't parse address")?;
    let backend_url = format!("{}/request", &opt.backend_url);
    let timeout = Duration::from_millis(opt.timeout);

    info!(
        "Starting the Trusted Shuffler server at {:?} with k = {} and {}",
        listen_address,
        opt.k,
        if timeout.is_zero() {
            String::from("no timeout")
        } else {
            format!("timeout {}", opt.timeout)
        }
    );

    let server =
        Server::bind(&listen_address).serve(ServiceBuilder::new(opt.k, timeout, &backend_url));
    tokio::select!(
        result = server => {
            result.context("Couldn't run server")?;
        },
        () = tokio::signal::ctrl_c().map(|r| r.unwrap()) => {
            info!("Stopping the Trusted Shuffler server");
        },
    );

    Ok(())
}
