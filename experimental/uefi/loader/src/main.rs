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
use futures::stream::StreamExt;
use log::info;
use qemu::{Qemu, QemuParams};
use tokio::{
    io::{self, AsyncReadExt, AsyncWriteExt},
    net::UnixStream,
    signal,
};
use tokio_util::codec::Decoder;
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
    env_logger::init();

    let (console_qemu, console) = UnixStream::pair()?;
    let (comms_qemu, comms) = UnixStream::pair()?;

    let qemu = Qemu::start(QemuParams {
        binary: cli.qemu.as_path(),
        firmware: cli.ovmf.as_path(),
        app: cli.uefi_app.as_path(),
        console: console_qemu,
        comms: comms_qemu,
    })?;

    // Log everything coming over the console channel.
    tokio::spawn(async {
        let codec = tokio_util::codec::LinesCodec::new();
        let mut framed = codec.framed(console);

        while let Some(line) = framed.next().await {
            // The UEFI console uses ANSI escape codes to clear screen and set colours, so
            // let's not just print the string out but rather the debug version of that.
            info!("console: {:?}", line.unwrap())
        }
    });

    // Bit hacky, but it's only temporary and turns out console I/O is complex.
    let (mut rh, mut wh) = comms.into_split();
    tokio::spawn(async move {
        let mut buf = [0; 1024];
        loop {
            let result = rh.read(&mut buf).await.unwrap();
            if result == 0 {
                break;
            } else {
                info!("rx: {:?}", &buf[..result]);
            }
        }
    });
    tokio::spawn(async move {
        let mut buf = [0; 1024];
        loop {
            let result = io::stdin().read(&mut buf).await.unwrap();
            if result == 0 {
                break;
            } else {
                info!("tx: {:?}", &buf[..result]);
                wh.write_all(&buf[..result]).await.unwrap();
            }
        }
    });

    signal::ctrl_c().await?;

    // Clean up.
    qemu.kill().await?;
    Ok(())
}
