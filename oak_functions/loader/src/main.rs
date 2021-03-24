//
// Copyright 2021 The Project Oak Authors
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

use structopt::StructOpt;

mod server;

use crate::server::WasmServer;

#[cfg(test)]
mod tests;

/// Command line options for the Oak loader.
#[derive(StructOpt, Clone, Debug)]
#[structopt(about = "Oak Functions Loader")]
pub struct Opt {
    #[structopt(long, default_value = "8080", help = "Server Port number.")]
    server_port: u16,
    #[structopt(
        long,
        help = "Path to a wasm file to be loaded and executed per invocation. The wasm module must export a function named `main`."
    )]
    wasm_path: String,
}

/// Main execution point for the Oak Functions Loader.
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    if cfg!(feature = "oak-unsafe") {
        env_logger::init();
    } else {
        eprintln!("No debugging output configured at build time");
    }
    let opt = Opt::from_args();

    // For now the server runs in the same thread, so `notify_sender` is not really needed.
    let (_notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    // Start HTTP server.
    let address = format!("[::]:{}", &opt.server_port);
    WasmServer::create(&address, &opt.wasm_path)?
        .start(notify_receiver)
        .await
}
