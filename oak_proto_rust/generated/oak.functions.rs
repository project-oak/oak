#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct InitializeRequest {
    #[prost(bytes = "vec", tag = "1")]
    pub wasm_module: ::prost::alloc::vec::Vec<u8>,
    #[prost(uint32, tag = "2")]
    pub constant_response_size: u32,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct InitializeResponse {
    #[prost(message, optional, tag = "2")]
    pub evidence: ::core::option::Option<super::attestation::v1::Evidence>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct InvokeRequest {
    #[prost(message, optional, tag = "2")]
    pub encrypted_request: ::core::option::Option<super::crypto::v1::EncryptedRequest>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct InvokeResponse {
    #[prost(message, optional, tag = "2")]
    pub encrypted_response: ::core::option::Option<super::crypto::v1::EncryptedResponse>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct LookupDataEntry {
    #[prost(bytes = "vec", tag = "1")]
    pub key: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "2")]
    pub value: ::prost::alloc::vec::Vec<u8>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct LookupDataChunk {
    #[prost(message, repeated, tag = "1")]
    pub items: ::prost::alloc::vec::Vec<LookupDataEntry>,
}
/// If the definition of ExtendNextLookupData changes, the estimation of the size
/// when serialized in the Oak Functions Launcher needs to change, too.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ExtendNextLookupDataRequest {
    #[prost(oneof = "extend_next_lookup_data_request::Data", tags = "1, 2")]
    pub data: ::core::option::Option<extend_next_lookup_data_request::Data>,
}
/// Nested message and enum types in `ExtendNextLookupDataRequest`.
pub mod extend_next_lookup_data_request {
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost_derive::Oneof)]
    pub enum Data {
        #[prost(message, tag = "1")]
        Chunk(super::LookupDataChunk),
        /// Experimental: a serialized array of varint-prefixed `LookupDataEntry`
        /// values. See
        /// <https://docs.rs/prost/latest/prost/fn.decode_length_delimiter.html> for
        /// more details; the hope here is that by serializing one entry at a time we
        /// can be more efficient.
        #[prost(bytes, tag = "2")]
        LengthDelimitedEntries(::prost::alloc::vec::Vec<u8>),
    }
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ExtendNextLookupDataResponse {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct FinishNextLookupDataRequest {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct FinishNextLookupDataResponse {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct AbortNextLookupDataResponse {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct Empty {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ReserveRequest {
    #[prost(uint64, tag = "1")]
    pub additional_entries: u64,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ReserveResponse {}
