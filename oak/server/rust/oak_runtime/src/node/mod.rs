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

use std::net::SocketAddr;
use std::string::String;
use std::sync::Arc;

use oak_abi::OakStatus;

use crate::runtime::RuntimeProxy;
use crate::Handle;

mod grpc_server;
mod logger;
mod wasm;

/// A trait implemented by every node and pseudo-node.
///
/// Nodes must not do any work until the [`Node::start`] method is invoked.
pub trait Node: Send + Sync {
    /// Starts executing the node.
    ///
    /// This method will be invoked in a blocking fashion by the [`Runtime`], therefore node
    /// implementations should make sure that they create separate background threads to execute
    /// actual work, and wait on them to terminate when [`Node::stop`] is called.
    fn start(&mut self) -> Result<(), OakStatus>;

    /// Stops executing the node.
    ///
    /// This method may block while the node terminates any outstanding work, but the node
    /// implementation must guarantee that it eventually returns.
    ///
    /// Internally, a node may implement this by first attempting to gracefully terminate, and then
    /// if that fails, continue trying with increasing level of aggressiveness.
    fn stop(&mut self);
}

/// A `Configuration` corresponds to an entry from a `ApplicationConfiguration`. It is the
/// static implementation specific configuration shared between instances.
pub enum Configuration {
    /// The configuration for a logging pseudo node.
    LogNode,

    /// The configuration for a gRPC server pseudo node that contains an `address` to listen on.
    GrpcServerNode { address: SocketAddr },

    /// The configuration for a Wasm node.
    // It would be better to store a list of exported methods and copyable Wasm interpreter
    // instance, but wasmi doesn't allow this. We make do with having a copyable
    // `Arc<wasmi::Module>` that we pass to new nodes, and clone to to spawn new
    // `wasmi::ModuleInstances`.
    WasmNode { module: Arc<wasmi::Module> },
}

/// A enumeration for errors occuring when building `Configuration` from protobuf types.
pub enum ConfigurationError {
    AddressParsingError(String),
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

/// Parses an `address` and checks if it's correct: TCP port should greater than 1023.
pub fn parse_server_address(address: &str) -> Result<SocketAddr, ConfigurationError> {
    address
        .parse()
        .map_err(|e| ConfigurationError::AddressParsingError(format!("{}", e)))
        .and_then(|parsed_address: SocketAddr| {
            if parsed_address.port() > 1023 {
                Ok(parsed_address)
            } else {
                Err(ConfigurationError::AddressParsingError(
                    "Server TCP port is <= 1023".to_string(),
                ))
            }
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
        reader: Handle,
        writer: Handle,
    ) -> Box<dyn Node> {
        match self {
            Configuration::LogNode => Box::new(logger::LogNode::new(config_name, runtime, reader)),
            Configuration::GrpcServerNode { address } => Box::new(
                grpc_server::GrpcServerNode::new(config_name, runtime, writer, *address),
            ),
            Configuration::WasmNode { module } => Box::new(wasm::WasmNode::new(
                config_name,
                runtime,
                module.clone(),
                entrypoint,
                reader,
            )),
        }
    }
}
