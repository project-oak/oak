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
    #[prost(oneof="node_configuration::ConfigType", tags="2, 3, 4, 5, 6")]
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
}
/// GrpcClientConfiguration describes the configuration of a gRPC client
/// pseudo-Node (which is provided by the Oak Runtime), connected to a specific
/// external (non-Oak) gRPC service.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GrpcClientConfiguration {
    /// The endpoint address of the external gRPC service.
    /// `address` is represented as an "ip_address:tcp_port" string.
    #[prost(string, tag="1")]
    pub address: std::string::String,
}
