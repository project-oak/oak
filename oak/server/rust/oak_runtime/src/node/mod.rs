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

use crate::{runtime::RuntimeProxy, GrpcConfiguration};
use oak_abi::proto::oak::application::{
    node_configuration::ConfigType, ApplicationConfiguration, LogConfiguration, NodeConfiguration,
};
use std::net::AddrParseError;
use tokio::sync::oneshot;

pub mod external;
mod grpc;
mod logger;
mod roughtime;
mod storage;
mod wasm;

/// Trait encapsulating execution of a Node or pseudo-Node.
pub trait Node: Send {
    /// Execute the Node, using the provided `Runtime` reference and initial handle.  The method
    /// should continue execution until the Node terminates.
    ///
    /// `notify_receiver` receives a notification from the Runtime upon termination. This
    /// notification can be used by the Node to gracefully shut down.
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        notify_receiver: oneshot::Receiver<()>,
    );
}

/// A enumeration for errors occuring when creating a new [`Node`] instance.
// TODO(#1027): Improve or delete this enum.
#[derive(Debug)]
pub enum ConfigurationError {
    AddressParsingError(AddrParseError),
    IncorrectPort,
    IncorrectURI,
    NoHostElement,
    CertificateParsingError,
    IncorrectWebAssemblyModuleName,
    InvalidNodeConfiguration,
    WasmiModuleInializationError(wasmi::Error),
}

impl From<AddrParseError> for ConfigurationError {
    fn from(error: AddrParseError) -> Self {
        ConfigurationError::AddressParsingError(error)
    }
}

impl std::fmt::Display for ConfigurationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            ConfigurationError::AddressParsingError(e) => {
                write!(f, "Failed to parse an address: {}", e)
            }
            ConfigurationError::IncorrectPort => write!(f, "Incorrect port (must be > 1023)"),
            ConfigurationError::IncorrectURI => write!(f, "Incorrect URI"),
            ConfigurationError::NoHostElement => write!(f, "URI doesn't contain the Host element"),
            ConfigurationError::CertificateParsingError => {
                write!(f, "Error parsing PEM encoded TLS certificate")
            }
            ConfigurationError::IncorrectWebAssemblyModuleName => {
                write!(f, "Incorrect WebAssembly module name")
            }
            ConfigurationError::InvalidNodeConfiguration => write!(f, "Invalid NodeConfiguration"),
            ConfigurationError::WasmiModuleInializationError(e) => {
                write!(f, "Failed to initialize wasmi::Module: {}", e)
            }
        }
    }
}

pub fn create_node(
    application_configuration: &ApplicationConfiguration,
    node_configuration: &NodeConfiguration,
    grpc_configuration: &GrpcConfiguration,
) -> Result<Box<dyn Node>, ConfigurationError> {
    let node_name = &node_configuration.name;
    match &node_configuration.config_type {
        Some(ConfigType::LogConfig(LogConfiguration {})) => {
            Ok(Box::new(logger::LogNode::new(node_name)))
        }
        Some(ConfigType::GrpcServerConfig(config)) => {
            Ok(Box::new(grpc::server::GrpcServerNode::new(
                node_name,
                config.clone(),
                grpc_configuration
                    .grpc_server_tls_identity
                    .as_ref()
                    .expect("no gRPC server TLS identity provided to Oak Runtime")
                    .clone(),
            )?))
        }
        Some(ConfigType::WasmConfig(config)) => Ok(Box::new(wasm::WasmNode::new(
            node_name,
            application_configuration,
            config.clone(),
        )?)),
        Some(ConfigType::GrpcClientConfig(config)) => {
            Ok(Box::new(grpc::client::GrpcClientNode::new(
                node_name,
                config.clone(),
                grpc_configuration
                    .grpc_client_root_tls_certificate
                    .as_ref()
                    .expect("no gRPC client root TLS certificate provided to Oak Runtime")
                    .clone(),
            )?))
        }
        Some(ConfigType::RoughtimeClientConfig(_config)) => {
            Ok(Box::new(roughtime::RoughtimeClientNode::new(node_name)))
        }
        Some(ConfigType::StorageConfig(_config)) => {
            Ok(Box::new(storage::StorageNode::new(node_name)))
        }
        None => Err(ConfigurationError::InvalidNodeConfiguration),
    }
}
