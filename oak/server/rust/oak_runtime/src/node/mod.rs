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

use crate::runtime::RuntimeProxy;
use log::debug;
use std::{
    net::{AddrParseError, SocketAddr},
    string::String,
    sync::Arc,
};
use tonic::transport::{Certificate, Identity, Uri};

pub mod external;
mod grpc;
mod logger;
mod wasm;

/// Trait encapsulating execution of a Node or pseudo-Node.
pub trait Node {
    /// Execute the Node, using the provided `Runtime` reference and initial handle.  The method
    /// should continue execution until the Node terminates.
    fn run(self: Box<Self>, runtime: RuntimeProxy, handle: oak_abi::Handle);
}

/// A `Configuration` corresponds to an entry from a `ApplicationConfiguration`. It is the
/// static implementation specific configuration shared between instances.
pub enum Configuration {
    /// The configuration for a logging pseudo-Node.
    LogNode,

    /// The configuration for a gRPC server pseudo-Node that contains an `address` to listen on and
    /// a TLS identity that consists of a private RSA key and an X.509 TLS certificate.
    GrpcServerNode {
        address: SocketAddr,
        tls_identity: Identity,
    },

    /// The configuration for a gRPC server pseudo-Node that contains a URI and an X.509 root TLS
    /// certificate.
    GrpcClientNode {
        uri: Uri,
        root_tls_certificate: Certificate,
        address: String,
    },

    /// The configuration for a Wasm Node.
    // It would be better to store a list of exported methods and copyable Wasm interpreter
    // instance, but wasmi doesn't allow this. We make do with having a copyable
    // `Arc<wasmi::Module>` that we pass to new Nodes, and clone to to spawn new
    // `wasmi::ModuleInstances`.
    WasmNode { module: Arc<wasmi::Module> },

    /// The configuration for an externally provided pseudo-Node.
    External,
}

/// A enumeration for errors occuring when building `Configuration` from protobuf types.
#[derive(Debug)]
pub enum ConfigurationError {
    AddressParsingError(AddrParseError),
    IncorrectPort,
    NoHostElement,
    CertificateParsingError,
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
            ConfigurationError::NoHostElement => write!(f, "URI doesn't contain the Host element"),
            ConfigurationError::CertificateParsingError => {
                write!(f, "Error parsing PEM encoded TLS certificate")
            }
            ConfigurationError::WasmiModuleInializationError(e) => {
                write!(f, "Failed to initialize wasmi::Module: {}", e)
            }
        }
    }
}

/// Loads a Wasm module into a Node configuration, returning an error if `wasmi` failed to load the
/// module.
pub fn load_wasm(wasm_bytes: &[u8]) -> Result<Configuration, ConfigurationError> {
    let module = wasmi::Module::from_buffer(wasm_bytes)
        .map_err(ConfigurationError::WasmiModuleInializationError)?;
    Ok(Configuration::WasmNode {
        module: Arc::new(module),
    })
}

/// Checks if port is greater than 1023.
pub fn check_port(address: &SocketAddr) -> Result<(), ConfigurationError> {
    if address.port() > 1023 {
        Ok(())
    } else {
        Err(ConfigurationError::IncorrectPort)
    }
}

/// Checks if URI contains the "Host" element.
pub fn check_uri(uri: &Uri) -> Result<(), ConfigurationError> {
    uri.authority()
        .filter(|authority| !authority.host().is_empty())
        .map(|_| ())
        .ok_or(ConfigurationError::NoHostElement)
}

/// Check the correctness of a PEM encoded TLS certificate.
pub fn load_certificate(certitiface: &str) -> Result<Certificate, ConfigurationError> {
    use rustls::internal::pemfile::certs;

    let mut cursor = std::io::Cursor::new(certitiface);
    // `rustls` doesn't specify certificate parsing errors:
    // https://docs.rs/rustls/0.17.0/rustls/internal/pemfile/fn.certs.html
    certs(&mut cursor).map_err(|_| ConfigurationError::CertificateParsingError)?;

    Ok(Certificate::from_pem(certitiface))
}

impl Configuration {
    /// Creates a new Node instance corresponding to the [`Configuration`].
    ///
    /// On success returns a boxed [`Node`] that can be run with [`Node::run`].
    pub fn create_node(
        &self,
        node_name: &str, // Used for pretty debugging
        config_name: &str,
        entrypoint: String,
    ) -> Option<Box<dyn Node + Send>> {
        debug!(
            "create_node('{}': '{}'.'{}')",
            node_name, config_name, entrypoint
        );
        match self {
            Configuration::LogNode => Some(Box::new(logger::LogNode::new(node_name))),
            Configuration::GrpcServerNode {
                address,
                tls_identity,
            } => Some(Box::new(grpc::server::GrpcServerNode::new(
                node_name,
                *address,
                tls_identity.clone(),
            ))),

            Configuration::GrpcClientNode {
                uri,
                root_tls_certificate,
                address: _,
            } => Some(Box::new(grpc::client::GrpcClientNode::new(
                node_name,
                uri.clone(),
                root_tls_certificate.clone(),
            ))),
            Configuration::WasmNode { module } => {
                match wasm::WasmNode::new(node_name, module.clone(), entrypoint) {
                    Some(node) => Some(Box::new(node)),
                    None => None,
                }
            }
            Configuration::External => {
                Some(Box::new(external::PseudoNode::new(node_name, config_name)))
            }
        }
    }

    pub fn node_subname(&self, entrypoint: &str) -> String {
        match self {
            Configuration::LogNode => "LogNode".to_string(),
            Configuration::GrpcServerNode { .. } => "GrpcServerNode".to_string(),
            Configuration::GrpcClientNode { .. } => "GrpcClientNode".to_string(),
            Configuration::WasmNode { .. } => format!("WasmNode-{}", entrypoint),
            Configuration::External => "ExternalPseudoNode".to_string(),
        }
    }
}
