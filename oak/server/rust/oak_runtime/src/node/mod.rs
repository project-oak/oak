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

use std::prelude::v1::*;

use std::string::String;
use std::sync::Arc;

use oak_abi::OakStatus;

use crate::channel::ChannelReader;
use crate::RuntimeRef;

mod logger;
mod wasm;

/// A `NodeConfiguration` corresponds to an entry from a `ApplicationConfiguration`. It is the
/// static implementation specific configuration shared between instances.
pub enum NodeConfiguration {
    /// The configuration for a logging pseudo node.
    LogNode,

    /// The configuration for a Wasm node.
    // It would be better to store a list of exported methods and copyable Wasm interpreter
    // instance, but wasmi doesn't allow this. We make do with having a copyable
    // `Arc<wasmi::Module>` that we pass to new nodes, and clone to to spawn new
    // `wasmi::ModuleInstances`.
    WasmNode { module: Arc<wasmi::Module> },
}

/// Loads a Wasm module into a node configuration.
// TODO(#564)
pub fn load_wasm(wasm_bytes: &[u8]) -> NodeConfiguration {
    let module = wasmi::Module::from_buffer(wasm_bytes).expect("failed to load wasm");
    NodeConfiguration::WasmNode {
        module: Arc::new(module),
    }
}

impl NodeConfiguration {
    /// Spawn a new node instance corresponding to the `NodeConfiguration` `self`. On success
    /// returns a `JoinHandle` to allow waiting on the thread to finish.
    pub fn new_instance(
        &self,
        config_name: &str, // Used for pretty debugging
        runtime: RuntimeRef,
        entrypoint: String,
        initial_reader: ChannelReader,
    ) -> Result<crate::JoinHandle, OakStatus> {
        match self {
            NodeConfiguration::LogNode => {
                logger::new_instance(config_name, runtime, initial_reader)
            }
            NodeConfiguration::WasmNode { module } => wasm::new_instance(
                config_name,
                runtime,
                module.clone(),
                entrypoint,
                initial_reader,
            ),
        }
    }
}
