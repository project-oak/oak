/// An ApplicationConfiguration represents a unit of deployment in Oak.
///
/// An Oak Application is built from a collection of interconnected Nodes,
/// each of which is running the code described by an entry in this
/// configuration.  These Nodes are created dynamically at runtime, with
/// the exception of the specified initial Node (which is created by the
/// Oak runtime).
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ApplicationConfiguration {
    /// Collection of available Node configurations, indexed by name (which must be
    /// unique across the collection).  Each Node in the application will run under
    /// a configuration that is identified by an entry in this collection.
    #[prost(message, repeated, tag="1")]
    pub node_configs: ::std::vec::Vec<NodeConfiguration>,
    /// Indication of what configuration the initial Node should run.  Must identify a
    /// NodeConfiguration entry that holds a WebAssemblyConfiguration object.
    #[prost(string, tag="2")]
    pub initial_node_config_name: std::string::String,
    /// The name of an exported Web Assembly function in the initial Node to
    /// be used as the Node's main entrypoint.
    #[prost(string, tag="3")]
    pub initial_entrypoint_name: std::string::String,
    /// Port number used by the gRPC pseudo-node; must be >= 1024.
    #[prost(int32, tag="4")]
    pub grpc_port: i32,
}
/// NodeConfiguration indicates the configuration of a created Node.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct NodeConfiguration {
    #[prost(string, tag="1")]
    pub name: std::string::String,
    #[prost(oneof="node_configuration::ConfigType", tags="2, 3, 4, 5, 6, 7")]
    pub config_type: ::std::option::Option<node_configuration::ConfigType>,
}
pub mod node_configuration {
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    pub enum ConfigType {
        #[prost(message, tag="2")]
        WasmConfig(super::WebAssemblyConfiguration),
        #[prost(message, tag="3")]
        LogConfig(super::LogConfiguration),
        #[prost(message, tag="4")]
        StorageConfig(super::StorageProxyConfiguration),
        #[prost(message, tag="5")]
        GrpcServerConfig(super::GrpcServerConfiguration),
        #[prost(message, tag="6")]
        GrpcClientConfig(super::GrpcClientConfiguration),
        #[prost(message, tag="7")]
        RoughtimeClientConfig(super::RoughtimeClientConfiguration),
    }
}
/// WebAssemblyConfiguration describes the configuration of a Web Assembly based Node.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct WebAssemblyConfiguration {
    /// The compiled code of the Oak Node, in WebAssembly binary format.
    /// See https://webassembly.org/docs/binary-encoding/ .
    /// TODO(#804): Replace this with just a hash of the bytecode to instantiate, and
    /// pass the actual bytecode to the Oak Manager in some other way.
    #[prost(bytes, tag="1")]
    pub module_bytes: std::vec::Vec<u8>,
}
/// LogConfiguration describes the configuration of a logging pseudo-Node (which
/// is provided by the Oak Runtime).
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LogConfiguration {
}
/// StorageProxyConfiguration describes the configuration of a storage proxy
/// pseudo-Node (which is provided by the Oak Runtime), connected to a specific
/// storage provider.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct StorageProxyConfiguration {
    /// The address of the external storage provider.
    #[prost(string, tag="1")]
    pub address: std::string::String,
}
/// GrpcServerConfiguration describes the configuration of a gRPC server
/// pseudo-Node (which is provided by the Oak Runtime), that processes gRPC
/// requests from external (non-Oak) clients.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GrpcServerConfiguration {
    /// The endpoint address for the gRPC server to listen on.
    /// `address` is represented as an "ip_address:tcp_port" string.
    #[prost(string, tag="1")]
    pub address: std::string::String,
    /// Loaded private RSA key file used by a gRPC server pseudo-Node.
    #[prost(string, tag="2")]
    pub grpc_tls_private_key: std::string::String,
    /// Loaded PEM encoded X.509 TLS certificate file used by a gRPC server pseudo-Node.
    #[prost(string, tag="3")]
    pub grpc_tls_certificate: std::string::String,
}
/// GrpcClientConfiguration describes the configuration of a gRPC client
/// pseudo-Node (which is provided by the Oak Runtime), connected to a specific
/// external (non-Oak) gRPC service.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GrpcClientConfiguration {
    /// The URI component of a gRPC server endpoint. Must contain the "Host" element.
    /// https://docs.rs/tonic/0.2.1/tonic/transport/struct.Uri.html
    #[prost(string, tag="1")]
    pub uri: std::string::String,
    /// Loaded PEM encoded X.509 TLS root certificate file used to authenticate an external gRPC
    /// service.
    #[prost(string, tag="2")]
    pub root_tls_certificate: std::string::String,
    /// The endpoint address of the external gRPC service.
    /// `address` is represented as an "ip_address:tcp_port" string.
    #[prost(string, tag="3")]
    pub address: std::string::String,
}
/// RoughtimeClientConfiguration describes the configuration of a Roughtime
/// client pseudo-Node (which is provided by the Oak Runtime), with the
/// given external Roughtime servers and connection parameters.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct RoughtimeClientConfiguration {
    /// The collection of Roughtime servers to query. A default set of servers
    /// will be used if this is empty.
    #[prost(message, repeated, tag="1")]
    pub servers: ::std::vec::Vec<RoughtimeServer>,
    /// Connection parameters; default values will be used if any parameter is
    /// zero.
    #[prost(int32, tag="2")]
    pub min_overlapping_intervals: i32,
    #[prost(int32, tag="3")]
    pub timeout_seconds: i32,
    #[prost(int32, tag="4")]
    pub server_retries: i32,
    #[prost(uint32, tag="5")]
    pub max_radius_microseconds: u32,
}
/// Information to identify a particular Roughtime server.
/// Only UDP and Ed25519 public keys are currently supported.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct RoughtimeServer {
    #[prost(string, tag="1")]
    pub name: std::string::String,
    #[prost(string, tag="2")]
    pub host: std::string::String,
    #[prost(uint32, tag="3")]
    pub port: u32,
    #[prost(string, tag="4")]
    pub public_key_base64: std::string::String,
}
/// A serialized list of key-value pairs that are specified as command line flags to the Oak Loader
/// binary, and are made available to the initial Node of the running Oak Application.
///
/// Keys are human readable strings and usually correspond to file names.
///
/// Values are raw binary blobs and usually correspond to file contents, which must be interpreted by
/// the running Oak Application.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConfigMap {
    #[prost(map="string, bytes", tag="1")]
    pub items: ::std::collections::HashMap<std::string::String, std::vec::Vec<u8>>,
}
