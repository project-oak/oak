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
use qemu::{Qemu, QemuParams};
use runtime::{Frame, FrameLength, FRAME_LENGTH_BYTES_SIZE};
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::UnixStream,
    signal,
};
use tokio_util::codec::Decoder;

mod qemu;
mod server;

#[derive(clap::ArgEnum, Clone, Debug, PartialEq)]
enum Mode {
    Uefi,
    Bios,
}

#[derive(Parser, Debug)]
struct Args {
    /// Path to the `qemu-system-x86_64` binary.
    #[clap(long, parse(from_os_str), validator = path_exists, default_value_os_t = PathBuf::from("/usr/bin/qemu-system-x86_64"))]
    qemu: PathBuf,

    /// Execute either in UEFI mode or BIOS mode.
    #[clap(arg_enum, long, default_value = "uefi")]
    mode: Mode,

    /// Path to the OVMF firmware file.
    #[clap(long, parse(from_os_str), required_if_eq("mode", "uefi"), validator = path_exists, default_value_os_t = PathBuf::from("/usr/share/OVMF/OVMF_CODE.fd"))]
    ovmf: PathBuf,

    /// Path to the UEFI app to execute.
    #[clap(parse(from_os_str), validator = path_exists)]
    app: PathBuf,
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
        firmware: if cli.mode == Mode::Uefi {
            Some(cli.ovmf.as_path())
        } else {
            None
        },
        app: cli.app.as_path(),
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
            log::info!("console: {:?}", line.unwrap())
        }
    });

    // TODO(#2709): Unfortunately OVMF writes some garbage (clear screen etc?) + our Hello
    // World to the other serial port, so let's skip some bytes before we set up framing.
    // The length of 71 characters has been determined experimentally and will change if we
    // change what we write to stdout in the UEFI app.
    if cli.mode == Mode::Uefi {
        let mut junk = [0; 71];
        comms.read_exact(&mut junk).await.unwrap();
        log::info!("Leading junk on comms: {:?}", std::str::from_utf8(&junk));
    }

    // Use a bmrng channel for serial communication. The good thing about spawning a separate
    // task for the serial communication is that it serializes (no pun intended) the communication,
    // as right now we don't have any mechanisms to track multiple requests in flight.
    let (tx, mut rx) = bmrng::unbounded_channel::<Vec<u8>, anyhow::Result<Vec<u8>>>();

    tokio::spawn(async move {
        async fn write_input_to_socket(
            wh: &mut tokio::net::unix::OwnedWriteHalf,
            input: Vec<u8>,
        ) -> anyhow::Result<()> {
            let encoded_frame = Frame { body: input }.encode()?;
            wh.write_all(&encoded_frame).await?;
            Ok(())
        }

        async fn read_frame_from_socket(
            rh: &mut tokio::net::unix::OwnedReadHalf,
        ) -> anyhow::Result<Frame> {
            let mut length_buf = [0; FRAME_LENGTH_BYTES_SIZE];
            rh.read_exact(&mut length_buf).await?;
            let length = FrameLength::from_be_bytes(length_buf);
            let mut body: Vec<u8> = vec![0; length.into()];
            rh.read_exact(&mut body).await?;
            Ok(Frame { body })
        }

        async fn respond(
            mut rh: &mut tokio::net::unix::OwnedReadHalf,
            mut wh: &mut tokio::net::unix::OwnedWriteHalf,
            input: Vec<u8>,
        ) -> anyhow::Result<Vec<u8>> {
            write_input_to_socket(&mut wh, input).await?;
            read_frame_from_socket(&mut rh)
                .await
                .and_then(|frame| Ok(frame.body))
        }

        let (mut rh, mut wh) = comms.into_split();
        while let Ok((input, responder)) = rx.recv().await {
            let response = respond(&mut rh, &mut wh, input).await;
            responder.respond(response).unwrap();
        }
    });

    let server_future = server::server("127.0.0.1:8000".parse()?, tx);

    // Wait until something dies or we get a signal to terminate.
    tokio::select! {
        _ = signal::ctrl_c() => {
            qemu.kill().await?;
        },
        _ = server_future => {
            qemu.kill().await?;
        },
        val = qemu.wait() => {
            log::error!("Unexpected qemu exit, status: {:?}", val);
        },
    }
    Ok(())
}
