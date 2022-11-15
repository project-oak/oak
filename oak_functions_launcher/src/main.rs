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

#![feature(never_type)]
#![feature(result_flattening)]

use anyhow::Context;
use clap::Parser;
use instance::{crosvm, native, LaunchedInstance};
use std::{
    fs,
    io::{BufRead, BufReader},
    net::{Ipv6Addr, SocketAddr},
    os::unix::net::UnixStream,
    path::PathBuf,
};
use tokio::signal;

pub mod schema {
    #![allow(dead_code)]
    use prost::Message;
    include!(concat!(env!("OUT_DIR"), "/oak.functions.rs"));
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
    #[command(subcommand)]
    mode: Mode,

    /// Consistent response size that the runtime should apply
    #[arg(long, default_value = "1024")]
    constant_response_size: u32,

    #[arg(long, default_value = "8080")]
    port: u16,

    /// Path to a Wasm file to be loaded into the trusted runtime and executed by it per
    /// invocation. See the documentation for details on its ABI. Ref: <https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md>
    #[arg(
        long,
        value_parser = path_exists,
    )]
    wasm: PathBuf,

    /// Path to a file containing key / value entries in protobuf binary format for lookup.
    #[arg(
        long,
        value_parser = path_exists,
    )]
    lookup_data: PathBuf,
}

fn path_exists(s: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(s);
    if !fs::metadata(s).map_err(|err| err.to_string())?.is_file() {
        Err(String::from("path does not represent a file"))
    } else {
        Ok(path)
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
            while reader.read_line(&mut line).expect("couldn't read line") > 0 {
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
                    lookup::load_lookup_data(&cli.lookup_data).expect("couldn't load lookup data");
                let encoded_lookup_data =
                    lookup::encode_lookup_data(lookup_data).expect("couldn't encode lookup data");

                if let Err(err) = runtime_client
                    .update_lookup_data(&encoded_lookup_data)
                    .await
                {
                    panic!("couldn't send lookup data: {:?}", err)
                }

                interval.tick().await;
            }
        });
    }

    let wasm_bytes = fs::read(&cli.wasm)
        .with_context(|| format!("couldn't read Wasm file {}", &cli.wasm.display()))
        .unwrap();
    log::info!(
        "read Wasm file from disk {} ({} bytes)",
        &cli.wasm.display(),
        wasm_bytes.len()
    );

    let request = schema::Initialization {
        wasm_module: wasm_bytes,
        constant_response_size: cli.constant_response_size,
    };

    let mut client = schema::TrustedRuntimeAsyncClient::new(connector_handle.clone());
    let result = client
        .initialize(&request)
        .await
        .flatten()
        .expect("couldn't initialize the runtime");

    let public_key_info = result.public_key_info.expect("no public key info returned");
    log::info!(
        "obtained public key ({} bytes)",
        public_key_info.public_key.len()
    );

    let server_future = server::server(
        SocketAddr::from((Ipv6Addr::UNSPECIFIED, cli.port)),
        connector_handle,
        public_key_info.public_key,
        public_key_info.attestation,
    );

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
