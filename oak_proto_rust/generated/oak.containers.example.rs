#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct HelloRequest {
    #[prost(message, optional, tag = "1")]
    pub encrypted_request: ::core::option::Option<
        super::super::crypto::v1::EncryptedRequest,
    >,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct HelloResponse {
    #[prost(message, optional, tag = "1")]
    pub encrypted_response: ::core::option::Option<
        super::super::crypto::v1::EncryptedResponse,
    >,
}
