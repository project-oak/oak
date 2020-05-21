/// Label represents information flowing through a Node or channel.
///
/// See https://pdos.csail.mit.edu/papers/flume-sosp07.pdf section 3.1.
#[derive(Clone, PartialEq, ::prost::Message)]
#[derive(Eq, Hash)]
pub struct Label {
    #[prost(message, repeated, tag="1")]
    pub confidentiality_tags: ::std::vec::Vec<Tag>,
    #[prost(message, repeated, tag="2")]
    pub integrity_tags: ::std::vec::Vec<Tag>,
}
/// Tag represents a category of confidentiality or integrity that is associated with data within
/// Oak, and refers to a Node or family of Nodes which are able to declassify data with that tag.
///
/// For instance, a tag may refer to a user connected over gRPC, or to the functionality implemented
/// by a WebAssembly Node, and this would require that data with those tags are declassified by the
/// respective node before they can leave Oak.
///
/// See https://pdos.csail.mit.edu/papers/flume-sosp07.pdf section 3.1.
#[derive(Clone, PartialEq, ::prost::Message)]
#[derive(Eq, Hash)]
pub struct Tag {
    #[prost(oneof="tag::Tag", tags="1, 2, 3")]
    pub tag: ::std::option::Option<tag::Tag>,
}
pub mod tag {
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    #[derive(Eq, Hash)]
    pub enum Tag {
        #[prost(message, tag="1")]
        GrpcTag(super::GrpcTag),
        #[prost(message, tag="2")]
        WebAssemblyModuleTag(super::WebAssemblyModuleTag),
        #[prost(message, tag="3")]
        TlsEndpointTag(super::TlsEndpointTag),
    }
}
/// Policies related to gRPC communication, referring to the native gRPC node within the TCB.
#[derive(Clone, PartialEq, ::prost::Message)]
#[derive(Eq, Hash)]
pub struct GrpcTag {
    /// In order for a client to be authorized to fulfill a tag with (public)
    /// `authorization_bearer_token_hmac` value h, the client needs to provide a (secret) bearer token
    /// s such that h = HMAC-SHA256(s, "oak-grpc-bearer-token-1").
    ///
    /// We don't use the raw token t as the tag itself because labels are considered public by default,
    /// so the confidentiality of the token would be compromised immediately.
    #[prost(bytes, tag="1")]
    pub authorization_bearer_token_hmac: std::vec::Vec<u8>,
}
/// Policies related to modules, referring to the native WebAssembly node within the TCB.
#[derive(Clone, PartialEq, ::prost::Message)]
#[derive(Eq, Hash)]
pub struct WebAssemblyModuleTag {
    /// The attestation for a single WebAssembly module, a SHA256 digest of the module in binary
    /// format.
    /// TODO(#630): Replace this with identity assertions for multiple module
    /// versions, based on a public verifiable log.
    #[prost(bytes, tag="1")]
    pub module_attestation: std::vec::Vec<u8>,
}
/// Policies related to HTTPS communication.
///
/// Applies to both the HTTP and gRPC client pseudo-nodes.
#[derive(Clone, PartialEq, ::prost::Message)]
#[derive(Eq, Hash)]
pub struct TlsEndpointTag {
    /// The Subject Alternative Name (SAN) of a certificate that a remote endpoint must be able to
    /// present in order to be allowed to receive data with this confidentiality tag.
    ///
    /// In general a certificate may have multiple SANs; an HTTP or gRPC client pseudo-node connected
    /// to a remote endpoint with multiple SANs is able to declassify data with a TlsEndpointTag
    /// referring to any of these SANs.
    ///
    /// The certificate is validated by the Oak Runtime using the set of Certificate Authorities (CA)
    /// that are available to it.
    ///
    /// See https://tools.ietf.org/html/rfc5280#section-4.2.1.6
    #[prost(string, tag="1")]
    pub certificate_subject_alternative_name: std::string::String,
}
