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
use futures::{stream::StreamExt, SinkExt};
use log::info;
use qemu::{Qemu, QemuParams};
use tokio::{io::AsyncReadExt, net::UnixStream, signal};
use tokio_serde_cbor::Codec;
use tokio_util::codec::Decoder;

mod qemu;
mod server;

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
    let (comms_qemu, mut comms) = UnixStream::pair()?;

    let mut qemu = Qemu::start(QemuParams {
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

    // TODO(#2709): Unfortunately OVMF writes some garbage (clear screen etc?) + our Hello
    // World to the other serial port, so let's skip some bytes before we set up the CBOR codec.
    // The length of 71 characters has been determined experimentally and will change if we
    // change what we write to stdout in the UEFI app.
    let mut junk = [0; 71];
    let mut len = 0;
    while len < junk.len() {
        len += comms.read(&mut junk[len..]).await.unwrap();
    }
    info!("Leading junk on comms: {:?}", std::str::from_utf8(&junk));

    // Use a bmrng channel for serial communication. The good thing about spawning a separate
    // task for the serial communication is that it serializes (no pun intended) the communication,
    // as right now we don't have any mechanisms to track multiple requests in flight.
    let (tx, mut rx) = bmrng::unbounded_channel::<String, anyhow::Result<String>>();

    tokio::spawn(async move {
        // Set up the CBOR codec to handle the comms.
        let codec: Codec<String, String> = Codec::new();
        let mut channel = codec.framed(comms);
        while let Ok((input, responder)) = rx.recv().await {
            responder
                .respond({
                    if let Err(err) = channel.send(input).await {
                        Err(anyhow::Error::from(err))
                    } else {
                        // TODO(#2726): Sometimes next() gives us a None. Figure out what's going on in there.
                        let mut response;
                        loop {
                            response = channel.next().await;
                            if response.is_some() {
                                break;
                            }
                        }
                        response.unwrap().map_err(anyhow::Error::from)
                    }
                })
                .unwrap();
        }
    });

    let server_future = server::server("127.0.0.1:8000".parse()?, tx);

    // Wait until something dies or we get a signal to terminate.
    tokio::select! {
        _ = signal::ctrl_c() => {},
        _ = server_future => {},
        _ = qemu.wait() => {},
    }
    // Clean up.
    qemu.kill().await?;
    Ok(())
}
