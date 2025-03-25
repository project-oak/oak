#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct TcpCommunicationChannel {
    /// Port to listen on. If not specified, defaults to 8080.
    #[prost(uint32, tag = "1")]
    pub port: u32,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct VsockCommunicationChannel {
    /// Port to listen on. If not specified, defaults to 8080.
    #[prost(uint32, tag = "1")]
    pub port: u32,
}
/// Settings specific to the Wasmtime engine.
///
/// These fields are explicitly marked as `optional` so that we could detect
/// their presence (as sometimes you do want to specify zero as a value). If a
/// field is left unspecified, it will leave whatever Wasmtime has as the
/// default.
///
/// See <https://docs.rs/wasmtime/latest/wasmtime/struct.Config.html> for more
/// details.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct WasmtimeConfig {
    /// If specified, switches to a pooling allocation strategy. If not specified,
    /// leaves as default (on demand).
    /// <https://docs.rs/wasmtime/latest/wasmtime/struct.Config.html#method.allocation_strategy>
    #[prost(message, optional, tag = "2")]
    pub pooling_strategy: ::core::option::Option<
        wasmtime_config::PoolingAllocationConfig,
    >,
    /// <https://docs.rs/wasmtime/latest/wasmtime/struct.Config.html#method.static_memory_maximum_size>
    #[prost(uint64, optional, tag = "3")]
    pub static_memory_maximum_size: ::core::option::Option<u64>,
    /// <https://docs.rs/wasmtime/latest/wasmtime/struct.Config.html#method.static_memory_guard_size>
    #[prost(uint64, optional, tag = "4")]
    pub static_memory_guard_size: ::core::option::Option<u64>,
    /// <https://docs.rs/wasmtime/latest/wasmtime/struct.Config.html#method.dynamic_memory_guard_size>
    #[prost(uint64, optional, tag = "5")]
    pub dynamic_memory_guard_size: ::core::option::Option<u64>,
    /// <https://docs.rs/wasmtime/latest/wasmtime/struct.Config.html#method.dynamic_memory_reserved_for_growth>
    #[prost(uint64, optional, tag = "6")]
    pub dynamic_memory_reserved_for_growth: ::core::option::Option<u64>,
    /// <https://docs.rs/wasmtime/latest/wasmtime/struct.Config.html#method.memory_init_cow>
    #[prost(bool, optional, tag = "7")]
    pub memory_init_cow: ::core::option::Option<bool>,
}
/// Nested message and enum types in `WasmtimeConfig`.
pub mod wasmtime_config {
    /// See
    /// <https://docs.rs/wasmtime/latest/wasmtime/struct.PoolingAllocationConfig.html>
    /// for a description of the various fields.
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost_derive::Message)]
    pub struct PoolingAllocationConfig {
        #[prost(uint32, optional, tag = "1")]
        pub max_unused_warm_slots: ::core::option::Option<u32>,
        #[prost(uint64, optional, tag = "2")]
        pub linear_memory_keep_resident: ::core::option::Option<u64>,
        #[prost(uint64, optional, tag = "3")]
        pub table_keep_resident: ::core::option::Option<u64>,
        #[prost(uint32, optional, tag = "4")]
        pub total_component_instances: ::core::option::Option<u32>,
        #[prost(uint64, optional, tag = "5")]
        pub max_component_instance_size: ::core::option::Option<u64>,
        #[prost(uint32, optional, tag = "6")]
        pub max_core_instances_per_component: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "7")]
        pub max_memories_per_component: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "8")]
        pub max_tables_per_component: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "9")]
        pub total_memories: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "10")]
        pub total_tables: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "11")]
        pub total_stacks: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "12")]
        pub total_core_instances: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "13")]
        pub max_core_instance_size: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "14")]
        pub max_tables_per_module: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "15")]
        pub table_elements: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "16")]
        pub max_memories_per_module: ::core::option::Option<u32>,
    }
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ApplicationConfig {
    /// How to load the provided module.
    #[prost(enumeration = "HandlerType", tag = "1")]
    pub handler_type: i32,
    /// Configuration for the Wasmtime engine, if that is used.
    /// Currently only used when running on Oak Containers; this field is ignored
    /// if we're using the wasmi or native engines.
    #[prost(message, optional, tag = "4")]
    pub wasmtime_config: ::core::option::Option<WasmtimeConfig>,
    /// Communication channel parameters.
    /// The default behaviour depends on the flavour of Oak Functions:
    ///    - when running on Restricted Kernel this setting is ignored completely as
    ///    the communication
    ///      channel is abstracted away by Restricted Kernel itself.
    ///    - on Oak Containers, if not specified, the default communication channel
    ///    is TCP.
    #[prost(oneof = "application_config::CommunicationChannel", tags = "2, 3")]
    pub communication_channel: ::core::option::Option<
        application_config::CommunicationChannel,
    >,
}
/// Nested message and enum types in `ApplicationConfig`.
pub mod application_config {
    /// Communication channel parameters.
    /// The default behaviour depends on the flavour of Oak Functions:
    ///    - when running on Restricted Kernel this setting is ignored completely as
    ///    the communication
    ///      channel is abstracted away by Restricted Kernel itself.
    ///    - on Oak Containers, if not specified, the default communication channel
    ///    is TCP.
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost_derive::Oneof)]
    pub enum CommunicationChannel {
        #[prost(message, tag = "2")]
        TcpChannel(super::TcpCommunicationChannel),
        #[prost(message, tag = "3")]
        VsockChannel(super::VsockCommunicationChannel),
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost_derive::Enumeration)]
#[repr(i32)]
pub enum HandlerType {
    /// Defaults to WASM.
    HandlerUnspecified = 0,
    /// Use a wasm interpreter to load the module.
    HandlerWasm = 1,
    /// Interpret the module as a native .so file. Only supported when running on
    /// Oak Containers.
    HandlerNative = 2,
}
impl HandlerType {
    /// String value of the enum field names used in the ProtoBuf definition.
    ///
    /// The values are not transformed in any way and thus are considered stable
    /// (if the ProtoBuf definition does not change) and safe for programmatic use.
    pub fn as_str_name(&self) -> &'static str {
        match self {
            HandlerType::HandlerUnspecified => "HANDLER_UNSPECIFIED",
            HandlerType::HandlerWasm => "HANDLER_WASM",
            HandlerType::HandlerNative => "HANDLER_NATIVE",
        }
    }
    /// Creates an enum from field names used in the ProtoBuf definition.
    pub fn from_str_name(value: &str) -> ::core::option::Option<Self> {
        match value {
            "HANDLER_UNSPECIFIED" => Some(Self::HandlerUnspecified),
            "HANDLER_WASM" => Some(Self::HandlerWasm),
            "HANDLER_NATIVE" => Some(Self::HandlerNative),
            _ => None,
        }
    }
}
