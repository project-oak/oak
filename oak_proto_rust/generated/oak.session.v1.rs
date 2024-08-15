/// Endorsed evidence contains an attestation evidence provided by the enclave
/// and the corresponding attestation endorsements provided by the hostlib.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct EndorsedEvidence {
    #[prost(message, optional, tag = "1")]
    pub evidence: ::core::option::Option<super::super::attestation::v1::Evidence>,
    #[prost(message, optional, tag = "2")]
    pub endorsements: ::core::option::Option<
        super::super::attestation::v1::Endorsements,
    >,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct GetEndorsedEvidenceRequest {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct GetEndorsedEvidenceResponse {
    #[prost(message, optional, tag = "1")]
    pub endorsed_evidence: ::core::option::Option<EndorsedEvidence>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct InvokeRequest {
    /// Body of the request, encrypted using Hybrid Public Key Encryption (HPKE).
    /// <<https://www.rfc-editor.org/rfc/rfc9180.html>>
    #[prost(message, optional, tag = "2")]
    pub encrypted_request: ::core::option::Option<
        super::super::crypto::v1::EncryptedRequest,
    >,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct InvokeResponse {
    /// Body of the request, encrypted using Hybrid Public Key Encryption (HPKE).
    /// <<https://www.rfc-editor.org/rfc/rfc9180.html>>
    #[prost(message, optional, tag = "2")]
    pub encrypted_response: ::core::option::Option<
        super::super::crypto::v1::EncryptedResponse,
    >,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct RequestWrapper {
    #[prost(oneof = "request_wrapper::Request", tags = "2, 3")]
    pub request: ::core::option::Option<request_wrapper::Request>,
}
/// Nested message and enum types in `RequestWrapper`.
pub mod request_wrapper {
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost_derive::Oneof)]
    pub enum Request {
        #[prost(message, tag = "2")]
        InvokeRequest(super::InvokeRequest),
        #[prost(message, tag = "3")]
        GetEndorsedEvidenceRequest(super::GetEndorsedEvidenceRequest),
    }
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ResponseWrapper {
    #[prost(oneof = "response_wrapper::Response", tags = "2, 3")]
    pub response: ::core::option::Option<response_wrapper::Response>,
}
/// Nested message and enum types in `ResponseWrapper`.
pub mod response_wrapper {
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost_derive::Oneof)]
    pub enum Response {
        #[prost(message, tag = "2")]
        InvokeResponse(super::InvokeResponse),
        #[prost(message, tag = "3")]
        GetEndorsedEvidenceResponse(super::GetEndorsedEvidenceResponse),
    }
}
/// Request message for the remote attestation.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct AttestRequest {
    /// Maps unique IDs of attestation providers to the corresponding evidence.
    #[prost(btree_map = "string, message", tag = "1")]
    pub endorsed_evidence: ::prost::alloc::collections::BTreeMap<
        ::prost::alloc::string::String,
        EndorsedEvidence,
    >,
}
/// Response message for the remote attestation.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct AttestResponse {
    /// Maps unique IDs of attestation providers to the corresponding evidence.
    #[prost(btree_map = "string, message", tag = "1")]
    pub endorsed_evidence: ::prost::alloc::collections::BTreeMap<
        ::prost::alloc::string::String,
        EndorsedEvidence,
    >,
}
/// Noise handshake message containing fields for all handshake patterns.
/// <<http://www.noiseprotocol.org/noise.html#handshake-patterns>>
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct NoiseHandshakeMessage {
    /// Noise Protocol ephemeral public key 'e'.
    /// <<http://www.noiseprotocol.org/noise.html#overview-of-handshake-state-machine>>
    #[prost(bytes = "vec", tag = "1")]
    pub ephemeral_public_key: ::prost::alloc::vec::Vec<u8>,
    /// Noise Protocol static public key 's'.
    /// <<http://www.noiseprotocol.org/noise.html#overview-of-handshake-state-machine>>
    ///
    /// Note: For some Noise patterns (such as XX and IX) static public key may be
    /// encrypted with the chaining key to hide peer's identity.
    /// <<http://www.noiseprotocol.org/noise.html#handshake-patterns>>
    #[prost(bytes = "vec", tag = "2")]
    pub static_public_key: ::prost::alloc::vec::Vec<u8>,
    /// Payload encrypted with the current chaining key.
    #[prost(bytes = "vec", tag = "3")]
    pub ciphertext: ::prost::alloc::vec::Vec<u8>,
}
/// Message to be signed as part of the attestation binding.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct AttestationBindingMessage {
    #[prost(bytes = "vec", tag = "1")]
    pub handshake_hash: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "2")]
    pub endorsements_hash: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "3")]
    pub peer_reference_values_hash: ::prost::alloc::vec::Vec<u8>,
}
/// Message that binds the Noise session (and optionally Attestation Endorsement
/// and peer Reference Values) to the Attestation Evidence.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct AttestationBinding {
    /// Signature of the serialized `AttestationBindingMessage` Protobuf message.
    #[prost(bytes = "vec", tag = "1")]
    pub signature: ::prost::alloc::vec::Vec<u8>,
}
/// Request message for the crypto handshake request needed to establish a set of
/// session keys.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct HandshakeRequest {
    #[prost(message, optional, tag = "2")]
    pub attestation_binding: ::core::option::Option<AttestationBinding>,
    #[prost(oneof = "handshake_request::HandshakeType", tags = "1")]
    pub handshake_type: ::core::option::Option<handshake_request::HandshakeType>,
}
/// Nested message and enum types in `HandshakeRequest`.
pub mod handshake_request {
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost_derive::Oneof)]
    pub enum HandshakeType {
        #[prost(message, tag = "1")]
        NoiseHandshakeMessage(super::NoiseHandshakeMessage),
    }
}
/// Response message for the crypto handshake request needed to establish a set
/// of session keys.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct HandshakeResponse {
    #[prost(message, optional, tag = "2")]
    pub attestation_binding: ::core::option::Option<AttestationBinding>,
    #[prost(oneof = "handshake_response::HandshakeType", tags = "1")]
    pub handshake_type: ::core::option::Option<handshake_response::HandshakeType>,
}
/// Nested message and enum types in `HandshakeResponse`.
pub mod handshake_response {
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost_derive::Oneof)]
    pub enum HandshakeType {
        #[prost(message, tag = "1")]
        NoiseHandshakeMessage(super::NoiseHandshakeMessage),
    }
}
/// Request message for the Oak protocol attested secure session.
/// This message is a wrapper containing different message types including:
/// attestation, handshake and encrypted data exchange.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct SessionRequest {
    #[prost(oneof = "session_request::Request", tags = "1, 2, 3")]
    pub request: ::core::option::Option<session_request::Request>,
}
/// Nested message and enum types in `SessionRequest`.
pub mod session_request {
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost_derive::Oneof)]
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
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct SessionResponse {
    #[prost(oneof = "session_response::Response", tags = "1, 2, 3")]
    pub response: ::core::option::Option<session_response::Response>,
}
/// Nested message and enum types in `SessionResponse`.
pub mod session_response {
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost_derive::Oneof)]
    pub enum Response {
        #[prost(message, tag = "1")]
        AttestResponse(super::AttestResponse),
        #[prost(message, tag = "2")]
        HandshakeResponse(super::HandshakeResponse),
        #[prost(bytes, tag = "3")]
        Ciphertext(::prost::alloc::vec::Vec<u8>),
    }
}
