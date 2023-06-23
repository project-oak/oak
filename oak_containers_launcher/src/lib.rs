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

mod qemu;

use clap::Parser;
use std::process;

#[derive(Parser, Debug)]
pub struct Args {
    #[arg(long, required = true)]
    vsock_cid: u32,
    #[arg(long, required = true)]
    vsock_port: u32,
    #[arg(long, required = true, value_parser = path_exists,)]
    system_image: std::path::PathBuf,
    #[arg(long, required = true, value_parser = path_exists,)]
    container_bundle: std::path::PathBuf,
    #[arg(long, value_parser = path_exists,)]
    application_config: Option<std::path::PathBuf>,
    #[command(flatten)]
    qemu_params: qemu::Params,
}

pub fn path_exists(s: &str) -> Result<std::path::PathBuf, String> {
    let path = std::path::PathBuf::from(s);
    if !std::fs::metadata(s)
        .map_err(|err| err.to_string())?
        .is_file()
    {
        Err(String::from("path does not represent a file"))
    } else {
        Ok(path)
    }
}

pub async fn create(args: Args) -> Result<(), anyhow::Error> {
    let server = oak_containers_launcher_server::new(
        args.vsock_cid,
        args.vsock_port,
        args.system_image,
        args.container_bundle,
        args.application_config,
    );

    // Use our PID for the CID of the guest.
    let mut vmm = qemu::Qemu::start(args.qemu_params, process::id())?;

    tokio::select! {
        _ = server => {}
        _ = vmm.wait() => {}
    }

    Ok(())
}
