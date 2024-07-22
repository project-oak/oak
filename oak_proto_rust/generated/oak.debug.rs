#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct CpuProfileRequest {
    #[prost(message, optional, tag = "1")]
    pub duration: ::core::option::Option<::prost_types::Duration>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct CpuProfileResponse {
    #[prost(message, optional, tag = "1")]
    pub profile: ::core::option::Option<super::super::perftools::profiles::Profile>,
}
