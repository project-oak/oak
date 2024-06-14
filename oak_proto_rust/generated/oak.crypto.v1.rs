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
