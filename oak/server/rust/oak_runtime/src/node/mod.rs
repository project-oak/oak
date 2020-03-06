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

use crate::runtime::ChannelReader;
use crate::RuntimeRef;

mod logger;
mod wasm;

/// A `Configuration` corresponds to an entry from a `ApplicationConfiguration`. It is the
/// static implementation specific configuration shared between instances.
pub enum Configuration {
    /// The configuration for a logging pseudo node.
    LogNode,

    /// The configuration for a Wasm node.
    // It would be better to store a list of exported methods and copyable Wasm interpreter
    // instance, but wasmi doesn't allow this. We make do with having a copyable
    // `Arc<wasmi::Module>` that we pass to new nodes, and clone to to spawn new
    // `wasmi::ModuleInstances`.
    WasmNode { module: Arc<wasmi::Module> },
}

/// A enumeration for errors occuring when building `Configuration` from protobuf types.
pub enum ConfigurationError {
    WasmiModuleInializationError(wasmi::Error),
}

impl std::fmt::Display for ConfigurationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            ConfigurationError::WasmiModuleInializationError(e) => {
                write!(f, "Failed to initialize wasmi::Module: {}", e)
            }
        }
    }
}

/// Loads a Wasm module into a node configuration, returning an error if `wasmi` failed to load the
/// module.
pub fn load_wasm(wasm_bytes: &[u8]) -> Result<Configuration, ConfigurationError> {
    let module = wasmi::Module::from_buffer(wasm_bytes)
        .map_err(ConfigurationError::WasmiModuleInializationError)?;
    Ok(Configuration::WasmNode {
        module: Arc::new(module),
    })
}

impl Configuration {
    /// Spawn a new node instance corresponding to the `Configuration` `self`. On success
    /// returns a `JoinHandle` to allow waiting on the thread to finish.
    pub fn new_instance(
        &self,
        config_name: &str, // Used for pretty debugging
        runtime: RuntimeRef,
        entrypoint: String,
        initial_reader: ChannelReader,
    ) -> Result<oak_platform::JoinHandle, OakStatus> {
        match self {
            Configuration::LogNode => logger::new_instance(config_name, runtime, initial_reader),
            Configuration::WasmNode { module } => wasm::new_instance(
                config_name,
                runtime,
                module.clone(),
                entrypoint,
                initial_reader,
            ),
        }
    }
}
