//
// Copyright 2020 The Project Oak Authors
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

use crate::application::ApplicationClient;
use anyhow::Context;
use async_trait::async_trait;
use maplit::hashmap;
use oak_abi::proto::oak::application::ConfigMap;
use std::collections::HashMap;
use trusted_database_client::proto::{
    trusted_database_client::TrustedDatabaseClient, GetPointOfInterestRequest,
};

const MAIN_MODULE_NAME: &str = "app";
const MAIN_ENTRYPOINT_NAME: &str = "oak_main";
const MAIN_MODULE_MANIFEST: &str = "../../examples/trusted_database/module/rust/Cargo.toml";
const MAIN_MODULE_WASM_FILE_NAME: &str = "trusted_database.wasm";

fn build_wasm() -> anyhow::Result<HashMap<String, Vec<u8>>> {
    Ok(hashmap! {
        MAIN_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(
            MAIN_MODULE_MANIFEST,
            MAIN_MODULE_WASM_FILE_NAME,
            oak_tests::Profile::Release
        ).context("Couldn't compile main module")?,
    })
}

pub struct OakApplication {
    runtime: std::sync::Arc<oak_runtime::Runtime>,
    client: TrustedDatabaseClient<tonic::transport::channel::Channel>,
}

impl OakApplication {
    pub async fn start(database: &str) -> Self {
        // Send test database as a start-of-day config map.
        let config_map = ConfigMap {
            items: hashmap! {"database".to_string() => database.as_bytes().to_vec()},
        };
        let wasm_modules = build_wasm().expect("Couldn't build wasm modules");
        let config = oak_tests::runtime_config_wasm(
            wasm_modules,
            MAIN_MODULE_NAME,
            MAIN_ENTRYPOINT_NAME,
            config_map,
            oak_runtime::SignatureTable::default(),
        );
        let runtime = oak_runtime::configure_and_run(config)
            .expect("Couldn't configure runtime with test wasm");

        let (channel, interceptor) = oak_tests::public_channel_and_interceptor().await;
        let client = TrustedDatabaseClient::with_interceptor(channel, interceptor);

        OakApplication { runtime, client }
    }

    pub fn stop(&self) {
        self.runtime.stop();
    }
}

#[async_trait]
impl ApplicationClient for OakApplication {
    /// Sends test requests to the oak application. Returns `()` since the value of the request is
    /// not needed for current benchmark implementation.
    async fn send_request(&mut self, id: &str) -> Result<(), tonic::Status> {
        let request = GetPointOfInterestRequest { id: id.to_string() };
        self.client.get_point_of_interest(request).await?;
        Ok(())
    }
}
