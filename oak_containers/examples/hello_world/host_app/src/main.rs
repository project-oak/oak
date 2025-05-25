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

use clap::Parser;
use oak_containers_examples_hello_world_host_app::{launcher_args::launcher_args, service};
use oak_file_utils::data_path;
use tokio::net::TcpListener;

#[derive(clap::ValueEnum, clap::Parser, Clone, Debug, Default)]
pub enum ServerType {
    #[default]
    Grpc,
    Rest,
}

#[derive(clap::Parser, Debug)]
#[group(skip)]
pub struct Args {
    #[command(flatten)]
    pub launcher_args: oak_containers_launcher::Args,
}

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    env_logger::init();

    let args = {
        let mut args = Args {
            launcher_args: launcher_args(data_path(
                "oak_containers/examples/hello_world/enclave_app/bundle.tar",
            ))
            .expect("failed to create launcher args"),
        };
        args.update_from(std::env::args_os());
        args
    };

    println!("ARGS: {args:?}");

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 8006);
    let listener = TcpListener::bind(addr).await?;

    println!("SERVER ADDR {:?}", listener.local_addr());

    service::create(listener, args.launcher_args).await
}
