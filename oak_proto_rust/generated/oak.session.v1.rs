/// Endorsed evidence contains an attestation evidence provided by the enclave
/// and the corresponding attestation endorsements provided by the hostlib.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct EndorsedEvidence {
    #[prost(message, optional, tag = "1")]
    pub evidence: ::core::option::Option<super::super::attestation::v1::Evidence>,
    #[prost(message, optional, tag = "2")]
    pub endorsements: ::core::option::Option<
        super::super::attestation::v1::Endorsements,
    >,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GetEndorsedEvidenceRequest {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GetEndorsedEvidenceResponse {
    #[prost(message, optional, tag = "1")]
    pub endorsed_evidence: ::core::option::Option<EndorsedEvidence>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct InvokeRequest {
    /// Body of the request, encrypted using Hybrid Public Key Encryption (HPKE).
    /// <<https://www.rfc-editor.org/rfc/rfc9180.html>>
    #[prost(message, optional, tag = "2")]
    pub encrypted_request: ::core::option::Option<
        super::super::crypto::v1::EncryptedRequest,
    >,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct InvokeResponse {
    /// Body of the request, encrypted using Hybrid Public Key Encryption (HPKE).
    /// <<https://www.rfc-editor.org/rfc/rfc9180.html>>
    #[prost(message, optional, tag = "2")]
    pub encrypted_response: ::core::option::Option<
        super::super::crypto::v1::EncryptedResponse,
    >,
}
/// Request message for the remote attestation.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct AttestRequest {
    #[prost(message, repeated, tag = "1")]
    pub endorsed_evidence: ::prost::alloc::vec::Vec<EndorsedEvidence>,
}
/// Request message for the remote attestation.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct AttestResponse {
    #[prost(message, repeated, tag = "1")]
    pub endorsed_evidence: ::prost::alloc::vec::Vec<EndorsedEvidence>,
}
/// Request message for the crypto handshake request needed to establish a set of
/// session keys.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct HandshakeRequest {
    /// Noise Protocol ephemeral public key 'e'.
    /// <<http://www.noiseprotocol.org/noise.html#overview-of-handshake-state-machine>>
    #[prost(bytes = "vec", tag = "1")]
    pub ephemeral_public_key: ::prost::alloc::vec::Vec<u8>,
    /// Payload encrypted with the current chaining key.
    #[prost(bytes = "vec", tag = "2")]
    pub ciphertext: ::prost::alloc::vec::Vec<u8>,
}
/// Response message for the crypto handshake request needed to establish a set
/// of session keys.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct HandshakeResponse {
    /// Noise Protocol ephemeral public key 'e'.
    /// <<http://www.noiseprotocol.org/noise.html#overview-of-handshake-state-machine>>
    #[prost(bytes = "vec", tag = "1")]
    pub ephemeral_public_key: ::prost::alloc::vec::Vec<u8>,
    /// Payload encrypted with the current chaining key.
    #[prost(bytes = "vec", tag = "2")]
    pub ciphertext: ::prost::alloc::vec::Vec<u8>,
}
/// Request message for the Oak protocol attested secure session.
/// This message is a wrapper containing different message types including:
/// attestation, handshake and encrypted data exchange.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SessionRequest {
    #[prost(oneof = "session_request::Request", tags = "1, 2, 3")]
    pub request: ::core::option::Option<session_request::Request>,
}
/// Nested message and enum types in `SessionRequest`.
pub mod session_request {
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    pub enum Request {
        #[prost(message, tag = "1")]
        AttestRequest(super::AttestRequest),
        #[prost(message, tag = "2")]
        HandshakeRequest(super::HandshakeRequest),
        #[prost(bytes, tag = "3")]
        Ciphertext(::prost::alloc::vec::Vec<u8>),
    }
}
/// Response message for the Oak protocol attested secure session.
/// This message is a wrapper containing different message types including:
/// attestation, handshake and encrypted data exchange.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SessionResponse {
    #[prost(oneof = "session_response::Response", tags = "1, 2, 3")]
    pub response: ::core::option::Option<session_response::Response>,
}
/// Nested message and enum types in `SessionResponse`.
pub mod session_response {
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    pub enum Response {
        #[prost(message, tag = "1")]
        AttestResponse(super::AttestResponse),
        #[prost(message, tag = "2")]
        HandshakeResponse(super::HandshakeResponse),
        #[prost(bytes, tag = "3")]
        Ciphertext(::prost::alloc::vec::Vec<u8>),
    }
}
