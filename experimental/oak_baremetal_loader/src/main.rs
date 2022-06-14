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

use clap::Parser;
use crosvm::Crosvm;
use oak_baremetal_communication_channel::{schema, InvocationChannel};
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

pub struct ClientHandler<T: ciborium_io::Read + ciborium_io::Write> {
    inner: InvocationChannel<T>,
}

impl<T> ClientHandler<T>
where
    T: ciborium_io::Read<Error = anyhow::Error> + ciborium_io::Write<Error = anyhow::Error>,
{
    pub fn new(inner: T) -> Self {
        Self {
            inner: InvocationChannel::new(inner),
        }
    }
}

impl<T> oak_idl::Handler for ClientHandler<T>
where
    T: ciborium_io::Read<Error = anyhow::Error> + ciborium_io::Write<Error = anyhow::Error>,
{
    fn invoke(&mut self, request: oak_idl::Request) -> Result<Vec<u8>, oak_idl::Status> {
        self.inner
            .write_message(request.into())
            .map_err(|_| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;

        let _x: Result<Vec<u8>, oak_idl::Status> = self
            .inner
            .read_message()
            .map_err(|_| oak_idl::Status::new(oak_idl::StatusCode::Internal))?
            .into();

        Ok(Vec::new())
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

    let mut comms = vmm.create_comms_channel()?;

    // TODO(#2709): Unfortunately OVMF writes some garbage (clear screen etc?) + our Hello
    // World to the other serial port, so let's skip some bytes before we set up framing.
    // The length of 71 characters has been determined experimentally and will change if we
    // change what we write to stdout in the UEFI app.
    if cli.mode == Mode::Uefi {
        let mut junk = [0; 71];
        comms.read_exact(&mut junk).unwrap();
        log::info!("Leading junk on comms: {:?}", std::str::from_utf8(&junk));
    }

    // Use a bmrng channel for serial communication. The good thing about spawning a separate
    // task for the serial communication is that it serializes (no pun intended) the communication,
    // as right now we don't have any mechanisms to track multiple requests in flight.
    let (tx, mut rx) = bmrng::unbounded_channel::<Vec<u8>, Result<Vec<u8>, oak_idl::Status>>();

    tokio::spawn(async move {
        let mut client = {
            let comms_channel = CommsChannel { inner: comms };
            let client_handler = ClientHandler::new(comms_channel);
            schema::TrustedRuntimeClient::new(client_handler)
        };

        let wasm_bytes = include_bytes!("echo.wasm");
        let initialization_message = {
            let mut builder = oak_idl::utils::MessageBuilder::default();
            let wasm_module = builder.create_vector::<u8>(wasm_bytes);
            let message = schema::Initialization::create(
                &mut builder,
                &schema::InitializationArgs {
                    wasm_module: Some(wasm_module),
                },
            );

            match builder.finish(message) {
                Ok(initialization_message) => initialization_message,
                Err(err) => panic!("errored when creating initialization message: {:?}", err),
            }
        };
        if let Err(err) = client.initialize(initialization_message.buf()) {
            panic!("failed to initialize the runtime: {:?}", err)
        }

        let mut respond = |input: Vec<u8>| -> Result<Vec<u8>, oak_idl::Status> {
            let request_message = oak_idl::utils::Message::<schema::UserRequest>::from_vec(input)
                .map_err(|err| {
                oak_idl::Status::new_with_message(oak_idl::StatusCode::Internal, err.to_string())
            })?;

            let response_message = client.handle_user_request(request_message.buf())?;

            let response_body = response_message
                .get()
                .body()
                .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;

            Ok(response_body.to_vec())
        };

        while let Ok((input, responder)) = rx.recv().await {
            let response = respond(input);
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
