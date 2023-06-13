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

mod image;
mod server;

use clap::Parser;
use std::{error::Error, net::SocketAddr};

#[derive(Parser, Debug)]
struct Args {
    #[arg(required = true)]
    addr: SocketAddr,

    #[arg(default_value = "/sbin/init")]
    init: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    // We want to send back a meaningful answer to the caller that the RPC has been handled
    // successfully. Thus, we need two channels: one to notify us that the image has been loaded,
    // and another so that we could shut down the gRPC server.
    let (shutdown_tx, shutdown_rx) = tokio::sync::oneshot::channel();
    let (loaded_tx, mut loaded_rx) = tokio::sync::mpsc::channel(1);

    let join = tokio::spawn(server::ImageLoaderServer::serve(
        args.addr,
        shutdown_rx,
        loaded_tx,
    ));
    let image = loaded_rx.recv().await.unwrap();
    shutdown_tx.send(()).unwrap();
    join.await??;

    // At this point we've shut down the server, so we expect that the response has been sent back
    // and the image has been unpacked into the correct directory. Switch roots and execute the
    // correct init.
    image.switch(&args.init)?;
}
