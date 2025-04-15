/// Certificate validity period.
///
/// Validity period is defined by 2 values: `not_before` and `not_after`. Both of
/// those values must be specified, and `not_before` timestamp must be strictly
/// earlier than `not_after`. Otherwise the certificate is considered invalid.
///
/// The validity period for a certificate is defined as the period of time from
/// `not_before` through `not_after`, inclusive.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct Validity {
    /// Timestamp on which the certificate validity period begins (inclusive).
    #[prost(message, optional, tag = "1")]
    pub not_before: ::core::option::Option<::prost_types::Timestamp>,
    /// Timestamp on which the certificate validity period ends (inclusive).
    #[prost(message, optional, tag = "2")]
    pub not_after: ::core::option::Option<::prost_types::Timestamp>,
}
/// Information about the public key that the certificate is issued for.
/// All fields of this message must be set. Otherwise the certificate is
/// considered invalid.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct SubjectPublicKeyInfo {
    /// Public key that this certificate is issued for.
    #[prost(bytes = "vec", tag = "1")]
    pub public_key: ::prost::alloc::vec::Vec<u8>,
    /// Purpose (key usage) ID that describes what private key (that subject public
    /// key corresponds to) is used for.
    /// It also describes it's parameters such as algorithm and serialization
    /// format.
    #[prost(bytes = "vec", tag = "2")]
    pub purpose_id: ::prost::alloc::vec::Vec<u8>,
}
/// Payload that is signed by the certificate.
/// All fields of this message must be set. Otherwise the certificate is
/// considered invalid.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct CertificatePayload {
    /// Certificate validity period.
    #[prost(message, optional, tag = "1")]
    pub validity: ::core::option::Option<Validity>,
    /// Public key that this certificate is issued for.
    #[prost(message, optional, tag = "2")]
    pub subject_public_key_info: ::core::option::Option<SubjectPublicKeyInfo>,
}
/// Information about the signature that signs the certificate.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct SignatureInfo {
    /// Signature value bytes.
    ///
    /// Signature format is defined by the Tink library (which includes the
    /// algorithm used to create this signature):
    /// <<https://developers.google.com/tink/wire-format#digital_signatures>>
    #[prost(bytes = "vec", tag = "1")]
    pub signature: ::prost::alloc::vec::Vec<u8>,
}
/// Minimalistic certificate proto definition.
///
/// Certificate is created as following:
/// - \[`CertificatePayload`\] proto message is serialized and signed using the
/// certificate authority's private key.
/// - This serialized message is stored in the `serialized_payload` field.
/// - The signature is stored in the `signature_info`.
///
/// The signature is created using the Tink library:
/// <<https://developers.google.com/tink/digital-signature>>
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct Certificate {
    /// Serialized \[`CertificatePayload`\] proto.
    #[prost(bytes = "vec", tag = "1")]
    pub serialized_payload: ::prost::alloc::vec::Vec<u8>,
    /// Signature that signs the certificate.
    #[prost(message, optional, tag = "2")]
    pub signature_info: ::core::option::Option<SignatureInfo>,
}
/// Request message encrypted using Hybrid Public Key Encryption (HPKE).
/// <<https://www.rfc-editor.org/rfc/rfc9180.html>>
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct EncryptedRequest {
    /// Message encrypted with Authenticated Encryption with Associated Data (AEAD)
    /// using the derived session key.
    #[prost(message, optional, tag = "1")]
    pub encrypted_message: ::core::option::Option<AeadEncryptedMessage>,
    /// Ephemeral Diffie-Hellman client public key that is needed to derive a
    /// session key. Only sent in the first message of the secure session.
    #[prost(bytes = "vec", optional, tag = "2")]
    pub serialized_encapsulated_public_key: ::core::option::Option<
        ::prost::alloc::vec::Vec<u8>,
    >,
}
/// Response message encrypted Hybrid Public Key Encryption (HPKE), which uses a
/// response key generated as part of bidirectional encryption.
/// <<https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>>
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct EncryptedResponse {
    /// Message encrypted with Authenticated Encryption with Associated Data (AEAD)
    /// using the derived session key.
    #[prost(message, optional, tag = "1")]
    pub encrypted_message: ::core::option::Option<AeadEncryptedMessage>,
}
/// Message encrypted with Authenticated Encryption with Associated Data (AEAD).
/// <<https://datatracker.ietf.org/doc/html/rfc5116>>
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct AeadEncryptedMessage {
    #[prost(bytes = "vec", tag = "1")]
    pub ciphertext: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "2")]
    pub associated_data: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "3")]
    pub nonce: ::prost::alloc::vec::Vec<u8>,
}
/// Envelope containing session keys required to encrypt/decrypt messages within
/// a secure session. Needed to serialize contexts in order to send them over an
/// RPC.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct SessionKeys {
    /// AEAD key for encrypting/decrypting client requests.
    #[prost(bytes = "vec", tag = "1")]
    pub request_key: ::prost::alloc::vec::Vec<u8>,
    /// AEAD key for encrypting/decrypting enclave responses.
    #[prost(bytes = "vec", tag = "4")]
    pub response_key: ::prost::alloc::vec::Vec<u8>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct Signature {
    #[prost(bytes = "vec", tag = "1")]
    pub signature: ::prost::alloc::vec::Vec<u8>,
}
