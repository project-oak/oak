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

#![feature(io_safety)]

use channel::{Frame, Framed};
use clap::Parser;
use crosvm::Crosvm;
use qemu::Qemu;
use std::{
    fs,
    io::{BufRead, BufReader, Read, Write},
    os::unix::net::UnixStream,
    path::PathBuf,
};
use tokio::signal;
use vmm::{Params, Vmm};

mod crosvm;
mod qemu;
mod server;
mod vmm;

#[derive(clap::ArgEnum, Clone, Debug, PartialEq)]
enum Mode {
    Uefi,
    Bios,
    Crosvm,
}

#[derive(Parser, Debug)]
struct Args {
    /// Path to the `qemu-system-x86_64` binary.
    #[clap(long, parse(from_os_str), validator = path_exists, default_value_os_t = PathBuf::from("/usr/bin/qemu-system-x86_64"))]
    qemu: PathBuf,

    /// Path to the `crosvm` binary.
    #[clap(long, parse(from_os_str), validator = path_exists, default_value_os_t = PathBuf::from("/usr/local/cargo/bin/crosvm"))]
    crosvm: PathBuf,

    /// Execution mode.
    #[clap(arg_enum, long, default_value = "uefi")]
    mode: Mode,

    /// Path to the OVMF firmware file.
    #[clap(long, parse(from_os_str), required_if_eq("mode", "uefi"), validator = path_exists, default_value_os_t = PathBuf::from("/usr/share/OVMF/OVMF_CODE.fd"))]
    ovmf: PathBuf,

    /// Path to the UEFI app or kernel to execute.
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

pub trait ReadWrite: Read + Write + Send + Sync {}

impl<T> ReadWrite for T where T: Read + Write + Send + Sync {}

struct CommsChannel {
    inner: Box<dyn ReadWrite>,
}

impl ciborium_io::Write for CommsChannel {
    type Error = anyhow::Error;
    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        self.inner.write_all(data).map_err(anyhow::Error::msg)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        self.inner.flush().map_err(anyhow::Error::msg)
    }
}

impl ciborium_io::Read for CommsChannel {
    type Error = anyhow::Error;

    fn read_exact(&mut self, data: &mut [u8]) -> Result<(), Self::Error> {
        self.inner.read_exact(data).map_err(anyhow::Error::msg)
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Args::parse();
    env_logger::init();

    let (console_vmm, console) = UnixStream::pair()?;

    let mut vmm: Box<dyn Vmm> = match cli.mode {
        Mode::Uefi => Box::new(Qemu::start(Params {
            binary: cli.qemu,
            firmware: Some(cli.ovmf),
            app: cli.app,
            console: console_vmm,
        })?),
        Mode::Bios => Box::new(Qemu::start(Params {
            binary: cli.qemu,
            firmware: None,
            app: cli.app,
            console: console_vmm,
        })?),
        Mode::Crosvm => Box::new(Crosvm::start(Params {
            binary: cli.crosvm,
            firmware: None,
            app: cli.app,
            console: console_vmm,
        })?),
    };

    // Log everything coming over the console channel.
    tokio::spawn(async {
        let mut reader = BufReader::new(console);

        let mut line = String::new();
        while reader.read_line(&mut line).expect("failed to read line") > 0 {
            // The UEFI console uses ANSI escape codes to clear screen and set colours, so
            // let's not just print the string out but rather the debug version of that.
            log::info!("console: {:?}", line);
            line.clear();
        }
    });

    let mut comms_channel = vmm.create_comms_channel()?;

    // TODO(#2709): Unfortunately OVMF writes some garbage (clear screen etc?) + our Hello
    // World to the other serial port, so let's skip some bytes before we set up framing.
    // The length of 71 characters has been determined experimentally and will change if we
    // change what we write to stdout in the UEFI app.
    if cli.mode == Mode::Uefi {
        let mut junk = [0; 71];
        comms_channel.read_exact(&mut junk).unwrap();
        log::info!("Leading junk on comms: {:?}", std::str::from_utf8(&junk));
    }

    // Use a bmrng channel for serial communication. The good thing about spawning a separate
    // task for the serial communication is that it serializes (no pun intended) the communication,
    // as right now we don't have any mechanisms to track multiple requests in flight.
    let (tx, mut rx) = bmrng::unbounded_channel::<Vec<u8>, anyhow::Result<Vec<u8>>>();

    let comms_channel = CommsChannel {
        inner: comms_channel,
    };
    tokio::spawn(async move {
        let mut framed = Framed::new(comms_channel);
        fn respond(framed: &mut Framed<CommsChannel>, input: Vec<u8>) -> anyhow::Result<Vec<u8>> {
            framed.write_frame(Frame { body: input })?;
            let response_frame = framed.read_frame()?;
            Ok(response_frame.body)
        }

        while let Ok((input, responder)) = rx.recv().await {
            let response = respond(&mut framed, input);
            responder.respond(response).unwrap();
        }
    });

    let server_future = server::server("127.0.0.1:8000".parse()?, tx);

    // Wait until something dies or we get a signal to terminate.
    tokio::select! {
        _ = signal::ctrl_c() => {
            vmm.kill().await?;
        },
        _ = server_future => {
            vmm.kill().await?;
        },
        val = vmm.wait() => {
            log::error!("Unexpected VMM exit, status: {:?}", val);
        },
    }

    Ok(())
}
