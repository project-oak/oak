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

use std::fmt::Display;
use std::string::String;
use std::sync::Arc;

use oak_abi::OakStatus;

use crate::runtime::RuntimeProxy;
use crate::Handle;

mod logger;
mod wasm;

/// A trait implemented by every node and pseudo-node.
///
/// Nodes must not do any work until the [`Node::start`] method is invoked.
pub trait Node: Display + Send {
    /// Starts executing the node.
    ///
    /// This method will be invoked in a blocking fashion by the [`Runtime`], therefore node
    /// implementations should make sure that they create separate background threads to execute
    /// actual work, and wait on them to terminate when [`Node::stop`] is called.
    fn start(&mut self) -> Result<(), OakStatus>;
}

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
    /// Creates a new node instance corresponding to the [`Configuration`] `self`.
    ///
    /// On success returns a boxed [`Node`] that may be started by invoking the [`Node::start`]
    /// method.
    pub fn create_node(
        &self,
        config_name: &str, // Used for pretty debugging
        runtime: RuntimeProxy,
        entrypoint: String,
        initial_reader: Handle,
    ) -> Box<dyn Node> {
        match self {
            Configuration::LogNode => {
                Box::new(logger::LogNode::new(config_name, runtime, initial_reader))
            }
            Configuration::WasmNode { module } => Box::new(wasm::WasmNode::new(
                config_name,
                runtime,
                module.clone(),
                entrypoint,
                initial_reader,
            )),
        }
    }
}
