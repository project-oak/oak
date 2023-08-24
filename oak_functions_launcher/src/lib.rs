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

mod lookup;
pub mod server;

pub mod proto {
    pub mod oak {
        pub mod functions {
            #![allow(dead_code)]
            use prost::Message;
            include!(concat!(env!("OUT_DIR"), "/oak.functions.rs"));
        }
        pub mod session {
            pub mod v1 {
                #![allow(clippy::return_self_not_must_use)]
                #![allow(clippy::large_enum_variant)]
                tonic::include_proto!("oak.session.v1");
            }
        }
    }
}

use crate::proto::oak::functions::{
    InitializeRequest, InitializeResponse, OakFunctionsAsyncClient,
};
use anyhow::Context;
use oak_launcher_utils::{
    channel::{self, ConnectorHandle},
    launcher,
};
use std::{fs, path::PathBuf, time::Duration};
use ubyte::ByteUnit;

pub struct LookupDataConfig {
    pub lookup_data_path: PathBuf,
    // Only periodically updates if interval is given.
    pub update_interval: Option<Duration>,
    pub max_chunk_size: ByteUnit,
}

pub async fn create(
    params: launcher::Params,
    lookup_data_config: LookupDataConfig,
    wasm_path: PathBuf,
    constant_response_size: u32,
) -> Result<
    (
        Box<dyn launcher::GuestInstance>,
        channel::ConnectorHandle,
        InitializeResponse,
    ),
    Box<dyn std::error::Error>,
> {
    log::info!("creating Oak Functions guest instance");
    let (launched_instance, connector_handle) = launcher::launch(params).await?;
    let intialize_response =
        intialize_enclave(connector_handle.clone(), &wasm_path, constant_response_size).await?;
    setup_lookup_data(connector_handle.clone(), lookup_data_config).await?;
    Ok((launched_instance, connector_handle, intialize_response))
}

// Initially loads lookup data and spawns task to periodically refresh lookup data.
async fn setup_lookup_data(
    connector_handle: channel::ConnectorHandle,
    config: LookupDataConfig,
) -> Result<(), Box<dyn std::error::Error>> {
    log::info!("setting up lookup data");
    let mut client = OakFunctionsAsyncClient::new(connector_handle);

    // Block for [invariant that lookup data is fully loaded](https://github.com/project-oak/oak/tree/main/oak_functions/lookup/README.md#invariant-fully-loaded-lookup-data)
    update_lookup_data(&mut client, &config).await?;

    // Spawn task to periodically refresh lookup data.
    if config.update_interval.is_some() {
        tokio::spawn(setup_periodic_update(client, config));
    }
    Ok(())
}

async fn setup_periodic_update(
    mut client: OakFunctionsAsyncClient<ConnectorHandle>,
    config: LookupDataConfig,
) {
    // Only set periodic update if an interval is given.
    let mut interval =
        tokio::time::interval(config.update_interval.expect("No update interval given."));
    loop {
        // Wait before updating because we just loaded the lookup data.
        interval.tick().await;
        let _ = update_lookup_data(&mut client, &config).await;
        // Ignore errors in updates of lookup data after the initial update.
    }
}

// Trigger loading of lookup data from lookup data source.
// Public for convenient testing.
pub async fn update_lookup_data(
    client: &mut OakFunctionsAsyncClient<ConnectorHandle>,
    config: &LookupDataConfig,
) -> anyhow::Result<()> {
    log::info!("updating lookup data");
    lookup::update_lookup_data(client, &config.lookup_data_path, config.max_chunk_size).await
}

// Loads application config (including Wasm bytes) into the enclave and returns a remote attestation
// evidence.
async fn intialize_enclave(
    connector_handle: channel::ConnectorHandle,
    wasm: &PathBuf,
    constant_response_size: u32,
) -> Result<InitializeResponse, Box<dyn std::error::Error>> {
    let wasm_bytes = fs::read(wasm)
        .with_context(|| format!("couldn't read Wasm file {}", wasm.display()))
        .unwrap();
    log::info!(
        "read Wasm file from disk {} ({})",
        &wasm.display(),
        ubyte::ByteUnit::Byte(wasm_bytes.len() as u64)
    );

    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size,
    };

    let mut client = OakFunctionsAsyncClient::new(connector_handle);
    log::info!("sending initialize request");
    let initialize_response = client
        .initialize(&request)
        .await
        .flatten()
        .expect("couldn't initialize service");
    log::info!("service initialized: {:?}", initialize_response);

    Ok(initialize_response)
}
