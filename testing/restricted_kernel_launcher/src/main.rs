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

#![feature(never_type)]
#![feature(result_flattening)]
#![feature(array_chunks)]

use clap::Parser;
use tokio::signal;

#[derive(Parser, Debug)]
pub struct Args {
    /// launcher params.
    #[clap(flatten)]
    launcher_params: oak_launcher_utils::launcher::Params,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Args::parse();
    env_logger::init();
    log::info!("Restricted Kernel Launcher args: {:?}", cli);

    let (mut launched_instance, _connector_handle) =
        restricted_kernel_launcher::create(cli.launcher_params).await?;

    // Wait until something dies or we get a signal to terminate.
    tokio::select! {
        _ = signal::ctrl_c() => {
            log::info!("Ctrl-C received, terminating VMM");
            launched_instance.kill().await?;
        },
        val = launched_instance.wait() => {
            log::error!("Unexpected VMM exit, status: {:?}", val);
        },
    }

    Ok(())
}
