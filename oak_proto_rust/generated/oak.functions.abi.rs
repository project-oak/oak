/// The client can check the configuration report for the configuration of the
/// Oak Functions runtime.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConfigurationReport {
    /// Hash of the loaded Wasm module.
    #[prost(bytes = "vec", tag = "1")]
    pub wasm_hash: ::prost::alloc::vec::Vec<u8>,
    /// The validated server-side policy.
    #[prost(message, optional, tag = "2")]
    pub policy: ::core::option::Option<ServerPolicy>,
}
/// / Server-side policy describing limits on the size of the response and
/// / response processing time to avoid side-channel leaks.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ServerPolicy {
    /// A fixed size for responses returned by the trusted runtime.
    ///
    /// This size only applies to the body of the Oak Functions response. If the
    /// response body computed by the Wasm module is smaller than this amount, it
    /// is padded with additional data before serialization and inclusion in the
    /// HTTP response to the client. If the body is larger than this amount, the
    /// trusted runtime discards the response and instead uses a response with a
    /// body of exactly this size, containing an error message indicating the
    /// policy violation. The body included in the HTTP response sent to the client
    /// is the binary protobuf encoding of the Oak Functions response, and will
    /// have a size larger than `constant_response_size_bytes`. However, this size
    /// is still guaranteed to be a constant.
    #[prost(uint32, tag = "1")]
    pub constant_response_size_bytes: u32,
    /// A fixed response time, in milliseconds.
    ///
    /// Similar to the previous one, but controls the amount of time the function
    /// is allowed to run for. If the function finishes before this time, the
    /// response is not sent back until the time is elapsed. If the function does
    /// not finish within this deadline, the trusted runtime sends a response to
    /// the client containing an error message indicating the failure. The size of
    /// this response is equal to the size specified by the previous parameter.
    #[prost(uint32, tag = "2")]
    pub constant_processing_time_ms: u32,
}
