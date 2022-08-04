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
use instance::{crosvm, native, LaunchedInstance};
use std::{
    fs,
    io::{BufRead, BufReader},
    os::unix::net::UnixStream,
    path::PathBuf,
};
use tokio::signal;

pub mod schema {
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/schema_services_servers.rs"));
    include!(concat!(
        env!("OUT_DIR"),
        "/schema_services_async_clients.rs"
    ));
}

mod channel;
mod instance;
mod lookup;
mod server;

#[derive(clap::Subcommand, Clone, Debug, PartialEq)]
enum Mode {
    /// Launch runtime in crosvm
    Crosvm(crosvm::Params),
    /// Launch a runtime binary directly as a child process
    Native(native::Params),
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
        Mode::Crosvm(params) => Box::new(crosvm::Instance::start(params, logs_console)?),
        Mode::Native(params) => Box::new(native::Instance::start(params)?),
    };

    let comms = launched_instance.create_comms_channel().await?;
    let connector_handle = channel::Connector::spawn(comms);

    // Spawn task to load & periodically refresh lookup data.
    {
        let mut runtime_client = schema::TrustedRuntimeAsyncClient::new(connector_handle.clone());
        tokio::spawn(async move {
            let mut interval =
                tokio::time::interval(std::time::Duration::from_millis(1000 * 60 * 10));
            loop {
                let lookup_data =
                    lookup::load_lookup_data(&cli.lookup_data).expect("failed to load lookup data");
                let encoded_lookup_data =
                    lookup::encode_lookup_data(lookup_data).expect("failed to encode lookup data");

                if let Err(err) = runtime_client
                    .update_lookup_data(encoded_lookup_data.into_vec())
                    .await
                {
                    panic!("failed to send lookup data: {:?}", err)
                }

                interval.tick().await;
            }
        });
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
    if let Err(err) = schema::TrustedRuntimeAsyncClient::new(connector_handle.clone())
        .initialize(owned_initialization_flatbuffer.into_vec())
        .await
    {
        panic!("failed to initialize the runtime: {:?}", err)
    }

    let server_future = server::server("127.0.0.1:8080".parse()?, connector_handle);

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
