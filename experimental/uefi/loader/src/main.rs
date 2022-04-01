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

use std::{fs, path::PathBuf};

use clap::Parser;
use qemu::Qemu;

mod qemu;

#[derive(Parser, Debug)]
struct Args {
    /// path to the `qemu-system-x86_64` binary
    #[clap(long, parse(from_os_str), validator = path_exists, default_value_os_t = PathBuf::from("/usr/bin/qemu-system-x86_64"))]
    qemu: PathBuf,

    /// path to the OVMF firmware file
    #[clap(long, parse(from_os_str), validator = path_exists, default_value_os_t = PathBuf::from("/usr/share/OVMF/OVMF_CODE.fd"))]
    ovmf: PathBuf,

    /// path to the UEFI app to execute
    #[clap(parse(from_os_str), validator = path_exists)]
    uefi_app: PathBuf,
}

fn path_exists(s: &str) -> Result<(), String> {
    if !fs::metadata(s).map_err(|err| err.to_string())?.is_file() {
        Err(String::from("Path does not represent a file"))
    } else {
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Args::parse();

    let qemu = Qemu::start(
        cli.qemu.as_path(),
        cli.ovmf.as_path(),
        cli.uefi_app.as_path(),
    )?;

    qemu.kill().await?;
    Ok(())
}
