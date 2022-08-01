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
use instance::LaunchedInstance;
use instance_binary::BinaryInstance;
use instance_crosvm::CrosvmInstance;
use instance_qemu::QemuInstance;
use oak_baremetal_communication_channel::{
    client::{ClientChannelHandle, RequestEncoder},
    schema,
};
use std::{
    fs,
    io::{BufRead, BufReader},
    os::unix::net::UnixStream,
    path::PathBuf,
};
use tokio::signal;

mod instance;
mod instance_binary;
mod instance_crosvm;
mod instance_qemu;
mod lookup;
mod server;

/// Parameters used for launching VM instances
#[derive(Parser, Clone, Debug, PartialEq)]
pub struct VmParams {
    /// Path to the VMM binary to execute.
    #[clap(long, parse(from_os_str), validator = path_exists)]
    pub vmm_binary: PathBuf,

    /// Path to the binary to load into the VM.
    #[clap(long, parse(from_os_str), validator = path_exists)]
    pub app_binary: PathBuf,

    /// Port to use for debugging with gdb
    #[clap(long = "gdb")]
    pub gdb: Option<u16>,
}

/// Parameters used for launching the runtime as a binary
#[derive(Parser, Clone, Debug, PartialEq)]
pub struct BinaryParams {
    /// Path to the runtime binary
    #[clap(long, parse(from_os_str), validator = path_exists)]
    pub app_binary: PathBuf,
}

#[derive(clap::Subcommand, Clone, Debug, PartialEq)]
enum Mode {
    /// Launch runtime in qemu
    Qemu(VmParams),
    /// Launch runtime in crosvm
    Crosvm(VmParams),
    /// Launch a runtime binary directly as a child process
    Binary(BinaryParams),
}

#[derive(Parser, Debug)]
struct Args {
    /// Execution mode.
    #[clap(subcommand)]
    mode: Mode,

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

/// Client implementation that communicates with the communication
/// task via a bmrng channel. Used by various parts of the loader to communicate
/// with the trusted runtime.
pub struct Client {
    request_dispatcher: bmrng::unbounded::UnboundedRequestSender<
        oak_idl::Request,
        Result<Vec<u8>, oak_idl::Status>,
    >,
}

#[async_trait::async_trait]
impl oak_idl::AsyncHandler for Client {
    async fn invoke(&mut self, request: oak_idl::Request) -> Result<Vec<u8>, oak_idl::Status> {
        self.request_dispatcher
            .send_receive(request)
            .await
            .map_err(|err| {
                oak_idl::Status::new_with_message(
                    oak_idl::StatusCode::Internal,
                    format!("failed when invoking the request_dispatcher: {}", err),
                )
            })?
    }
}

/// Singleton responsible for sending requests, and receiving responses over the underlying
/// communication channel with the baremetal runtime.
pub struct BaremetalCommunicationChannel {
    inner: ClientChannelHandle,
    request_encoder: RequestEncoder,
}

impl BaremetalCommunicationChannel {
    pub fn new(inner: Box<dyn oak_baremetal_communication_channel::Channel>) -> Self {
        Self {
            inner: ClientChannelHandle::new(inner),
            request_encoder: RequestEncoder::default(),
        }
    }

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

    // Provide a way for the launched instance to send logs
    let logs_console: UnixStream = {
        // Create two linked consoles. Technically both can read/write, but we'll
        // use them as a one way channel.
        let (console_writer, console_receiver) = UnixStream::pair()?;

        // Log everything sent by the writer.
        tokio::spawn(async {
            let mut reader = BufReader::new(console_receiver);

            let mut line = String::new();
            while reader.read_line(&mut line).expect("failed to read line") > 0 {
                log::info!("console: {:?}", line);
                line.clear();
            }
        });

        console_writer
    };

    let mut launched_instance: Box<dyn LaunchedInstance> = match cli.mode {
        Mode::Qemu(params) => Box::new(QemuInstance::start(params, logs_console)?),
        Mode::Crosvm(params) => Box::new(CrosvmInstance::start(params, logs_console)?),
        Mode::Binary(params) => Box::new(BinaryInstance::start(params)?),
    };

    let comms = launched_instance.create_comms_channel().await?;

    // A message based communication channel that permits other parts of the
    // untrusted launcher to send requests to the task that handles communicating
    // with the runtime and receive responses.
    let (request_dispatcher, mut request_receiver) =
        bmrng::unbounded_channel::<oak_idl::Request, Result<Vec<u8>, oak_idl::Status>>();

    // Spawn task to handle communicating with the runtime and receiving responses.
    tokio::spawn(async move {
        let mut communication_channel = BaremetalCommunicationChannel::new(comms);
        while let Ok((request, response_dispatcher)) = request_receiver.recv().await {
            // At the moment requests are sent sequentially, and in FIFO order. The next request
            // is sent only once a response to the previous message has been implemented.
            // TODO(#2848): Implement message prioritization, and non sequential invocations.
            let response = communication_channel.invoke(request);
            response_dispatcher.respond(response).unwrap();
        }
    });

    let mut lookup_data_client = schema::TrustedRuntimeAsyncClient::new(Client {
        request_dispatcher: request_dispatcher.clone(),
    });
    // Spawn task to load & periodically refresh lookup data.
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(std::time::Duration::from_millis(1000 * 60 * 10));

        loop {
            let lookup_data =
                lookup::load_lookup_data(&cli.lookup_data).expect("failed to load lookup data");
            let encoded_lookup_data =
                lookup::encode_lookup_data(lookup_data).expect("failed to encode lookup data");

            if let Err(err) = lookup_data_client
                .update_lookup_data(encoded_lookup_data.into_vec())
                .await
            {
                panic!("failed to send lookup data: {:?}", err)
            }

            interval.tick().await;
        }
    });

    let mut client = schema::TrustedRuntimeAsyncClient::new(Client {
        request_dispatcher: request_dispatcher.clone(),
    });

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
    if let Err(err) = client
        .initialize(owned_initialization_flatbuffer.into_vec())
        .await
    {
        panic!("failed to initialize the runtime: {:?}", err)
    }

    let server_future = server::server("127.0.0.1:8080".parse()?, request_dispatcher);

    // Wait until something dies or we get a signal to terminate.
    tokio::select! {
        _ = signal::ctrl_c() => {
            launched_instance.kill().await?;
        },
        _ = server_future => {
            launched_instance.kill().await?;
        },
        val = launched_instance.wait() => {
            log::error!("Unexpected VMM exit, status: {:?}", val);
        },
    }

    Ok(())
}
