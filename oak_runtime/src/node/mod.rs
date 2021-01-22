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

//! Functionality for different Node types.

use crate::{
    permissions::PermissionsConfiguration, NodePrivilege, RuntimeProxy, SecureServerConfiguration,
    SignatureTable,
};
use oak_abi::proto::oak::application::{
    node_configuration::ConfigType, ApplicationConfiguration, CryptoConfiguration,
    LogConfiguration, NodeConfiguration,
};
use std::net::AddrParseError;
use tokio::sync::oneshot;

mod crypto;
pub mod grpc;
pub mod http;
mod invocation;
mod logger;
mod roughtime;
mod storage;
mod wasm;

/// Trait encapsulating execution of a Node or pseudo-Node.
pub trait Node: Send {
    /// Returns a name for this type of Node.
    fn node_type(&self) -> &'static str;

    /// Returns a value indicating the isolation of a Node. If a Node is sandboxed (e.g. a Wasm
    /// node), the sandbox restricts external communcations. Uncontrolled nodes (e.g pseudo Nodes
    /// that are part of the runtime) have no restrictions enforced on external communications.
    ///
    /// Unless a node uses a trusted sandbox to restrict communications this function should always
    /// return [`NodeIsolation::Uncontrolled`]
    fn isolation(&self) -> NodeIsolation {
        NodeIsolation::Uncontrolled
    }

    /// Executes the Node, using the provided `Runtime` reference and initial handle.  The method
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

    /// Gets the privilege associated with the Node.
    fn get_privilege(&self) -> NodePrivilege {
        NodePrivilege::default()
    }
}

/// Indication of the level of isolation of a node.
#[derive(Debug)]
pub enum NodeIsolation {
    Sandboxed,
    Uncontrolled,
}

/// A enumeration for errors occurring when creating a new [`Node`] instance.
// TODO(#1027): Improve or delete this enum.
#[derive(Debug)]
pub enum ConfigurationError {
    AddressParsingError(AddrParseError),
    IncorrectPort,
    IncorrectURI,
    NoHostElement,
    IncorrectWebAssemblyModuleName,
    InvalidNodeConfiguration,
    WasmiModuleInializationError(wasmi::Error),
    NodeCreationNotPermitted,
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
            ConfigurationError::IncorrectWebAssemblyModuleName => {
                write!(f, "Incorrect WebAssembly module name")
            }
            ConfigurationError::InvalidNodeConfiguration => write!(f, "Invalid NodeConfiguration"),
            ConfigurationError::WasmiModuleInializationError(e) => {
                write!(f, "Failed to initialize wasmi::Module: {}", e)
            }
            ConfigurationError::NodeCreationNotPermitted => {
                write!(f, "Node creation not permitted")
            }
        }
    }
}

/// Implementation of [`NodeFactory`] for server-like Oak applications running on cloud
/// environments with WebAssembly support.
pub struct ServerNodeFactory {
    pub application_configuration: ApplicationConfiguration,
    pub permissions_configuration: PermissionsConfiguration,
    pub secure_server_configuration: SecureServerConfiguration,
    pub signature_table: SignatureTable,
}

impl NodeFactory<NodeConfiguration> for ServerNodeFactory {
    fn create_node(
        &self,
        node_name: &str,
        node_configuration: &NodeConfiguration,
    ) -> Result<Box<dyn Node>, ConfigurationError> {
        if !self
            .permissions_configuration
            .allowed_creation(&node_configuration)
            // TODO(#1027): Use anyhow or an improved ConfigurationError
            .map_err(|_| ConfigurationError::InvalidNodeConfiguration)?
        {
            return Err(ConfigurationError::NodeCreationNotPermitted);
        }

        match &node_configuration.config_type {
            Some(ConfigType::CryptoConfig(CryptoConfiguration {})) => {
                Ok(Box::new(crypto::CryptoNode::new(node_name)))
            }
            Some(ConfigType::LogConfig(LogConfiguration {})) => {
                Ok(Box::new(logger::LogNode::new(node_name)))
            }
            Some(ConfigType::GrpcServerConfig(config)) => {
                let grpc_configuration = self
                    .secure_server_configuration
                    .grpc_config
                    .clone()
                    .expect("no gRPC identity provided to Oak Runtime");
                Ok(Box::new(grpc::server::GrpcServerNode::new(
                    node_name,
                    config.clone(),
                    grpc_configuration
                        .grpc_server_tls_identity
                        .as_ref()
                        .expect("no gRPC server TLS identity provided to Oak Runtime")
                        .clone(),
                    grpc_configuration.oidc_client_info.clone(),
                )?))
            }
            Some(ConfigType::WasmConfig(config)) => Ok(Box::new(wasm::WasmNode::new(
                node_name,
                &self.application_configuration,
                config.clone(),
                &self.signature_table,
            )?)),
            Some(ConfigType::GrpcClientConfig(config)) => {
                let grpc_client_root_tls_certificate = self
                    .secure_server_configuration
                    .clone()
                    .grpc_config
                    .expect("no gRPC identity provided to Oak Runtime")
                    .grpc_client_root_tls_certificate
                    .expect("no root TLS certificate provided to Oak Runtime");
                Ok(Box::new(grpc::client::GrpcClientNode::new(
                    node_name,
                    config.clone(),
                    grpc_client_root_tls_certificate,
                )?))
            }
            Some(ConfigType::RoughtimeClientConfig(config)) => Ok(Box::new(
                roughtime::RoughtimeClientNode::new(node_name, config),
            )),
            Some(ConfigType::StorageConfig(_config)) => {
                Ok(Box::new(storage::StorageNode::new(node_name)))
            }
            Some(ConfigType::HttpServerConfig(config)) => {
                let tls_config = self
                    .secure_server_configuration
                    .http_config
                    .clone()
                    .expect("no TLS configuration for HTTP servers provided to Oak Runtime")
                    .tls_config;
                Ok(Box::new(http::server::HttpServerNode::new(
                    node_name,
                    config.clone(),
                    tls_config,
                )?))
            }
            Some(ConfigType::HttpClientConfig(config)) => {
                let http_client_root_tls_certificate = self
                    .secure_server_configuration
                    .http_config
                    .clone()
                    .expect("no HTTP configuration provided to Oak Runtime")
                    .http_client_root_tls_certificate
                    .expect("no root TLS certificate provided to Oak Runtime");
                Ok(Box::new(http::client::HttpClientNode::new(
                    node_name,
                    config.clone(),
                    http_client_root_tls_certificate,
                )?))
            }
            None => Err(ConfigurationError::InvalidNodeConfiguration),
        }
    }
}

/// A trait implemented by a concrete factory of nodes that creates nodes based on a Node
/// configuration of type `T`.
pub trait NodeFactory<T> {
    /// Creates a new [`Node`] instance with the specified name and based on the provided Node
    /// configuration information.
    fn create_node(
        &self,
        node_name: &str,
        node_configuration: &T,
    ) -> Result<Box<dyn Node>, ConfigurationError>;
}
