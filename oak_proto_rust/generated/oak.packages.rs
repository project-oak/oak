/// A single package and its associated version IDs.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct Package {
    /// The name of the package.
    #[prost(string, tag = "1")]
    pub name: ::prost::alloc::string::String,
    /// The version IDs of the package.
    #[prost(string, repeated, tag = "2")]
    pub version_ids: ::prost::alloc::vec::Vec<::prost::alloc::string::String>,
}
/// List of published packages.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct PackageList {
    #[prost(message, repeated, tag = "1")]
    pub packages: ::prost::alloc::vec::Vec<Package>,
}
