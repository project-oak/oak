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
#![feature(array_chunks)]

use crate::channel::ConnectorHandle;
use anyhow::Context;
use instance::{native, virtualized, LaunchedInstance};
use std::{
    fs,
    io::{BufRead, BufReader},
    os::unix::net::UnixStream,
    path::PathBuf,
};

use crate::schema::InitializeResponse;

pub mod schema {
    #![allow(dead_code)]
    use prost::Message;
    include!(concat!(env!("OUT_DIR"), "/oak.functions.rs"));
}

mod channel;
pub mod instance;
mod lookup;
pub mod server;

#[derive(clap::Subcommand, Clone, Debug, PartialEq)]
pub enum Mode {
    /// Launch a virtual enclave binary
    Virtual(virtualized::Params),
    /// Launch an enclave binary directly as a child process
    Native(native::Params),
}

pub async fn create(
    mode: Mode,
    lookup_data_path: PathBuf,
    wasm_path: PathBuf,
    constant_response_size: u32,
) -> Result<
    (
        Box<dyn LaunchedInstance>,
        ConnectorHandle,
        InitializeResponse,
    ),
    Box<dyn std::error::Error>,
> {
    let (launched_instance, connector_handle) = launch_instance(mode).await?;
    setup_lookup_data(connector_handle.clone(), lookup_data_path).await?;
    let intialization_response =
        setup_wasm(connector_handle.clone(), &wasm_path, constant_response_size).await?;
    Ok((launched_instance, connector_handle, intialization_response))
}

async fn launch_instance(
    mode: Mode,
) -> Result<(Box<dyn LaunchedInstance>, ConnectorHandle), Box<dyn std::error::Error>> {
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

    let launched_instance: Box<dyn LaunchedInstance> = match mode {
        Mode::Virtual(params) => Box::new(virtualized::Instance::start(params, logs_console)?),
        Mode::Native(params) => Box::new(native::Instance::start(params)?),
    };
    let comms = launched_instance.create_comms_channel().await?;
    let connector_handle = channel::Connector::spawn(comms);

    Ok((launched_instance, connector_handle))
}

// Initially loads lookup data and spawns task to periodically refresh lookup data.
async fn setup_lookup_data(
    connector_handle: ConnectorHandle,
    lookup_data_path: PathBuf,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut client = schema::OakFunctionsAsyncClient::new(connector_handle);

    // Block for [invariant that lookup data is fully loaded](https://github.com/project-oak/oak/tree/main/oak_functions/lookup/README.md#invariant-fully-loaded-lookup-data)
    lookup::update_lookup_data(&mut client, &lookup_data_path).await?;

    // Spawn task to periodically refresh lookup data.
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(std::time::Duration::from_millis(1000 * 60 * 10));
        loop {
            // Wait before updating because we just loaded the lookup data.
            interval.tick().await;
            let _ = lookup::update_lookup_data(&mut client, &lookup_data_path).await;
            // Ignore errors in updates of lookup data after the initial update.
        }
    });
    Ok(())
}

// Loads wasm bytes.
async fn setup_wasm(
    connector_handle: ConnectorHandle,
    wasm: &PathBuf,
    constant_response_size: u32,
) -> Result<InitializeResponse, Box<dyn std::error::Error>> {
    let wasm_bytes = fs::read(wasm)
        .with_context(|| format!("couldn't read Wasm file {}", wasm.display()))
        .unwrap();
    log::info!(
        "read Wasm file from disk {} ({} bytes)",
        &wasm.display(),
        wasm_bytes.len()
    );

    let request = schema::InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size,
    };

    let mut client = schema::OakFunctionsAsyncClient::new(connector_handle);
    let initialize_response = client
        .initialize(&request)
        .await
        .flatten()
        .expect("couldn't initialize the service");

    Ok(initialize_response)
}
