// This file is @generated by prost-build.
#[derive(Clone, Copy, PartialEq, ::prost::Message)]
pub struct ReadRequestRequest {}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ReadRequestResponse {
    #[prost(bytes = "vec", tag = "1")]
    pub body: ::prost::alloc::vec::Vec<u8>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct WriteResponseRequest {
    #[prost(bytes = "vec", tag = "1")]
    pub body: ::prost::alloc::vec::Vec<u8>,
}
#[derive(Clone, Copy, PartialEq, ::prost::Message)]
pub struct WriteResponseResponse {}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LogRequest {
    #[prost(string, tag = "1")]
    pub message: ::prost::alloc::string::String,
}
#[derive(Clone, Copy, PartialEq, ::prost::Message)]
pub struct LogResponse {}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LookupDataRequest {
    #[prost(bytes = "vec", tag = "1")]
    pub key: ::prost::alloc::vec::Vec<u8>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LookupDataResponse {
    #[prost(message, optional, tag = "1")]
    pub value: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LookupDataMultiRequest {
    #[prost(bytes = "vec", repeated, tag = "1")]
    pub keys: ::prost::alloc::vec::Vec<::prost::alloc::vec::Vec<u8>>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LookupDataMultiResponse {
    #[prost(message, repeated, tag = "1")]
    pub values: ::prost::alloc::vec::Vec<BytesValue>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct TestRequest {
    #[prost(bytes = "vec", tag = "1")]
    pub body: ::prost::alloc::vec::Vec<u8>,
    /// Whether to echo the message back. If false, the response will be empty.
    #[prost(bool, tag = "2")]
    pub echo: bool,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct TestResponse {
    #[prost(bytes = "vec", tag = "1")]
    pub body: ::prost::alloc::vec::Vec<u8>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct BytesValue {
    #[prost(bytes = "vec", tag = "1")]
    pub value: ::prost::alloc::vec::Vec<u8>,
    /// If true, the value was found in the store. This is useful to distinguish
    /// between a value that was not found and a value that was found and is empty.
    #[prost(bool, tag = "2")]
    pub found: bool,
}
