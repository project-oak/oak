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
use log::warn;
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
    pub kms_credentials: Option<std::path::PathBuf>,
}

impl NodeFactory<NodeConfiguration> for ServerNodeFactory {
    fn create_node(
        &self,
        node_name: &str,
        node_configuration: &NodeConfiguration,
    ) -> Result<CreatedNode, ConfigurationError> {
        if !self
            .permissions_configuration
            .allowed_creation(node_configuration)
            // TODO(#1027): Use anyhow or an improved ConfigurationError
            .map_err(|_| ConfigurationError::InvalidNodeConfiguration)?
        {
            return Err(ConfigurationError::NodeCreationNotPermitted);
        }

        match &node_configuration.config_type {
            Some(ConfigType::CryptoConfig(CryptoConfiguration {})) => Ok(CreatedNode {
                instance: Box::new(crypto::CryptoNode::new(
                    node_name,
                    self.kms_credentials.clone(),
                )),
                // TODO(#1842): sort out IFC interactions so that the crypto pseudo-Node can receive
                // labelled plaintext data and emit unlabelled encrypted data (which would probably
                // mean top_privilege() goes here).
                privilege: NodePrivilege::default(),
            }),
            Some(ConfigType::LogConfig(LogConfiguration {})) => Ok(CreatedNode {
                instance: Box::new(logger::LogNode::new(node_name)),

                // Allow the logger Node to declassify log messages in debug builds only.
                #[cfg(feature = "oak-unsafe")]
                privilege: NodePrivilege::top_privilege(),

                // The logger must not have any declassification privilege in non-debug builds.
                #[cfg(not(feature = "oak-unsafe"))]
                privilege: NodePrivilege::default(),
            }),
            Some(ConfigType::GrpcServerConfig(config)) => {
                let grpc_configuration = self
                    .secure_server_configuration
                    .grpc_config
                    .clone()
                    .expect("no gRPC identity provided to Oak Runtime");
                Ok(CreatedNode {
                    instance: Box::new(grpc::server::GrpcServerNode::new(
                        node_name,
                        config.clone(),
                        grpc_configuration
                            .grpc_server_tls_identity
                            .as_ref()
                            .expect("no gRPC server TLS identity provided to Oak Runtime")
                            .clone(),
                        grpc_configuration.oidc_client_info.clone(),
                    )?),
                    // This node needs to have `top` privilege to be able to declassify data tagged
                    // with any arbitrary user identities.
                    // TODO(#1631): When we have a separate top for each sub-lattice, this should be
                    // changed to the top of the identity sub-lattice.
                    privilege: NodePrivilege::top_privilege(),
                })
            }
            Some(ConfigType::WasmConfig(config)) => {
                let wasm_module_bytes = self
                    .application_configuration
                    .wasm_modules
                    .get(&config.wasm_module_name)
                    .ok_or(ConfigurationError::IncorrectWebAssemblyModuleName)?;
                Ok(CreatedNode {
                    instance: Box::new(wasm::WasmNode::new(
                        node_name,
                        wasm_module_bytes,
                        config.clone(),
                    )?),
                    privilege: wasm::get_privilege(wasm_module_bytes, &self.signature_table),
                })
            }
            Some(ConfigType::GrpcClientConfig(config)) => {
                let grpc_client_root_tls_certificate = self
                    .secure_server_configuration
                    .clone()
                    .grpc_config
                    .expect("no gRPC identity provided to Oak Runtime")
                    .grpc_client_root_tls_certificate
                    .expect("no root TLS certificate provided to Oak Runtime");
                let uri = config.uri.parse().map_err(|err| {
                    warn!("could not parse URI {}: {:?}", config.uri, err);
                    ConfigurationError::IncorrectURI
                })?;
                Ok(CreatedNode {
                    instance: Box::new(grpc::client::GrpcClientNode::new(
                        node_name,
                        &uri,
                        grpc_client_root_tls_certificate,
                    )?),
                    privilege: grpc::client::get_privilege(&uri),
                })
            }
            Some(ConfigType::RoughtimeClientConfig(config)) => Ok(CreatedNode {
                instance: Box::new(roughtime::RoughtimeClientNode::new(node_name, config)),
                privilege: NodePrivilege::default(),
            }),
            Some(ConfigType::StorageConfig(_config)) => Ok(CreatedNode {
                instance: Box::new(storage::StorageNode::new(node_name)),
                privilege: NodePrivilege::default(),
            }),
            Some(ConfigType::HttpServerConfig(config)) => {
                let tls_config = self
                    .secure_server_configuration
                    .http_config
                    .clone()
                    .expect("no TLS configuration for HTTP servers provided to Oak Runtime")
                    .tls_config;
                Ok(CreatedNode {
                    instance: Box::new(http::server::HttpServerNode::new(
                        node_name,
                        config.clone(),
                        tls_config,
                    )?),
                    // This node needs to have `top` privilege to be able to declassify data tagged
                    // with any arbitrary user identities.
                    // TODO(#1631): When we have a separate top for each sub-lattice, this should be
                    // changed to the top of the `identity` sub-lattice.
                    privilege: NodePrivilege::top_privilege(),
                })
            }
            Some(ConfigType::HttpClientConfig(config)) => {
                let http_client_root_tls_certificate = self
                    .secure_server_configuration
                    .http_config
                    .clone()
                    .expect("no HTTP configuration provided to Oak Runtime")
                    .http_client_root_tls_certificate
                    .expect("no root TLS certificate provided to Oak Runtime");
                Ok(CreatedNode {
                    instance: Box::new(http::client::HttpClientNode::new(
                        node_name,
                        config.clone(),
                        http_client_root_tls_certificate,
                    )?),
                    privilege: http::client::get_privilege(&config.authority),
                })
            }
            None => Err(ConfigurationError::InvalidNodeConfiguration),
        }
    }
}

/// A holder struct containing a [`Node`] instance, together with the [`NodePrivilege`] that is
/// assigned to it.
///
/// The reason the privilege is returned here and not by the node itself is that it should be
/// determined by the [`NodeFactory`] instance, so that an untrusted Node may not be able to
/// single-handedly increase its own privilege. In this codebase all the Nodes are defined alongside
/// each other, so this does not make much difference, but if Nodes were loaded dynamically or from
/// untrusted libraries, then it would be more obvious that we would still want to keep the
/// privilege assignment here.
pub struct CreatedNode {
    pub instance: Box<dyn Node>,
    pub privilege: NodePrivilege,
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
    ) -> Result<CreatedNode, ConfigurationError>;
}

// the `linear-handles` feature makes [`Sender`] and [`Receiver`] non-`Copy`, so we must use `Clone`
// with the feature turned on. But doing so with the feature off will make clippy complain, so we
// have this simple function that always uses the appropriate impl for copying these types.
// TODO(#1854): Remove this once linear-handles are the default.
#[cfg(not(feature = "linear-handles"))]
pub(crate) fn copy_or_clone<T: Copy>(t: &T) -> T {
    *t
}

#[cfg(feature = "linear-handles")]
pub(crate) fn copy_or_clone<T: Clone>(t: &T) -> T {
    t.clone()
}
