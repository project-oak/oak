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

use anyhow::Context;
use clap::Parser;
use crosvm::Crosvm;
use oak_baremetal_communication_channel::{
    client::{ClientChannelHandle, RequestEncoder},
    schema,
};
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
mod lookup;
mod qemu;
mod server;
mod vmm;

#[derive(clap::ArgEnum, Clone, Debug, PartialEq)]
enum Mode {
    Qemu,
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
    #[clap(arg_enum, long, default_value = "qemu")]
    mode: Mode,

    /// Path to the kernel to execute.
    #[clap(long, parse(from_os_str), validator = path_exists)]
    app: PathBuf,

    /// Path to a Wasm file to be loaded into the trusted runtime and executed by it per
    /// invocation. See the documentation for details on its ABI. Ref: <https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md>
    #[clap(
        long,
        parse(from_os_str),
        validator = path_exists,
    )]
    wasm: PathBuf,

    /// Path to a file containing key / value entries in protobuf binary format for lookup.
    #[clap(
        long,
        parse(from_os_str),
        validator = path_exists,
    )]
    lookup_data: PathBuf,
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

impl oak_baremetal_communication_channel::Write for CommsChannel {
    fn write(&mut self, data: &[u8]) -> anyhow::Result<()> {
        self.inner.write_all(data).map_err(anyhow::Error::msg)
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        self.inner.flush().map_err(anyhow::Error::msg)
    }
}

impl oak_baremetal_communication_channel::Read for CommsChannel {
    fn read(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        self.inner.read_exact(data).map_err(anyhow::Error::msg)
    }
}

pub struct ClientHandler {
    inner: ClientChannelHandle,
    request_encoder: RequestEncoder,
}

impl ClientHandler {
    pub fn new(inner: Box<dyn oak_baremetal_communication_channel::Channel>) -> Self {
        Self {
            inner: ClientChannelHandle::new(inner),
            request_encoder: RequestEncoder::default(),
        }
    }
}

impl oak_idl::Handler for ClientHandler {
    fn invoke(&mut self, request: oak_idl::Request) -> Result<Vec<u8>, oak_idl::Status> {
        let request_message = self.request_encoder.encode_request(request);
        let request_message_invocation_id = request_message.invocation_id;
        self.inner
            .write_request(request_message)
            .map_err(|_| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;

        let response_message = self
            .inner
            .read_response()
            .map_err(|_| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;

        // For now all messages are sent in sequence, hence we expect that the
        // id of the next response matches the preceeding request.
        // TODO(#2848): Allow messages to be sent and received out of order.
        assert_eq!(
            request_message_invocation_id,
            response_message.invocation_id
        );

        response_message.into()
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Args::parse();
    env_logger::init();

    let (console_vmm, console) = UnixStream::pair()?;

    let mut vmm: Box<dyn Vmm> = match cli.mode {
        Mode::Qemu => Box::new(Qemu::start(Params {
            binary: cli.qemu,
            app: cli.app,
            console: console_vmm,
        })?),
        Mode::Crosvm => Box::new(Crosvm::start(Params {
            binary: cli.crosvm,
            app: cli.app,
            console: console_vmm,
        })?),
    };

    // Log everything coming over the console channel.
    tokio::spawn(async {
        let mut reader = BufReader::new(console);

        let mut line = String::new();
        while reader.read_line(&mut line).expect("failed to read line") > 0 {
            log::info!("console: {:?}", line);
            line.clear();
        }
    });

    let comms = vmm.create_comms_channel().await?;

    // A message based communication channel that permits other parts of the
    // untrusted loader to send requests to the tasks that handles communicating
    // with the runtime and receive responses. Requests and (ok) responses
    // sent over this channel represent flatbuffer encoded messages. This is
    // done as it is not possible to send the flatbuffer Message structs
    // themselves over the channel.
    let (request_dispatcher, mut request_receiver) =
        bmrng::unbounded_channel::<Vec<u8>, Result<Vec<u8>, oak_idl::Status>>();

    // Spawn task that handles communication with the trusted runtime.
    tokio::spawn(async move {
        let mut client = {
            let comms_channel = Box::new(CommsChannel { inner: comms });
            let client_handler = ClientHandler::new(comms_channel);
            schema::TrustedRuntimeClient::new(client_handler)
        };

        let lookup_data =
            lookup::load_lookup_data(&cli.lookup_data).expect("failed to load lookup data");
        let encoded_lookup_data =
            lookup::encode_lookup_data(lookup_data).expect("failed to encode lookup data");

        if let Err(err) = client.update_lookup_data(encoded_lookup_data.buf()) {
            panic!("failed to send lookup data: {:?}", err)
        }

        let wasm_bytes = fs::read(&cli.wasm)
            .with_context(|| format!("Couldn't read Wasm file {}", &cli.wasm.display()))
            .unwrap();
        let owned_initialization_flatbuffer = {
            let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
            let wasm_module = builder.create_vector::<u8>(&wasm_bytes);
            let initialization_flatbuffer = schema::Initialization::create(
                &mut builder,
                &schema::InitializationArgs {
                    wasm_module: Some(wasm_module),
                },
            );

            builder
                .finish(initialization_flatbuffer)
                .expect("errored when creating initialization message")
        };
        if let Err(err) = client.initialize(owned_initialization_flatbuffer.buf()) {
            panic!("failed to initialize the runtime: {:?}", err)
        }

        while let Ok((encoded_request, response_dispatcher)) = request_receiver.recv().await {
            let response = client
                .handle_user_request(&encoded_request)
                .map(|oak_idl_message| oak_idl_message.into_vec());
            response_dispatcher.respond(response).unwrap();
        }
    });

    let server_future = server::server("127.0.0.1:8080".parse()?, request_dispatcher);

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
