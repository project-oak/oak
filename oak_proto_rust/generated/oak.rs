/// Contains various digest formats for the same underlying file. Mixing
/// digests from various files is "undefined behavior". There is no distinction
/// between empty and not set, it means the same.
///
/// The wire numbers are the codec IDs in
/// <https://github.com/multiformats/multicodec/blob/master/table.csv>
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct RawDigest {
    #[prost(bytes = "vec", tag = "16")]
    pub psha2: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "17")]
    pub sha1: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "18")]
    pub sha2_256: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "19")]
    pub sha2_512: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "20")]
    pub sha3_512: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "21")]
    pub sha3_384: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "22")]
    pub sha3_256: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "23")]
    pub sha3_224: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "32")]
    pub sha2_384: ::prost::alloc::vec::Vec<u8>,
}
/// Similar to RawDigest, but contains hex-encoded hashes for the sake of better
/// readability and copy-pastability. The set of all possible RawDigest and the
/// set of all possible HexDigests are in a bijective correspondence, by just
/// hex-encoding or hex-decoding each field separately.
///
/// For example, the field sha2_256 could contain
/// "82aac1adbfe3ada1244c1f54b7c949519e1f048067d0c3b236b7ae048fc7e227".
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct HexDigest {
    #[prost(string, tag = "16")]
    pub psha2: ::prost::alloc::string::String,
    #[prost(string, tag = "17")]
    pub sha1: ::prost::alloc::string::String,
    #[prost(string, tag = "18")]
    pub sha2_256: ::prost::alloc::string::String,
    #[prost(string, tag = "19")]
    pub sha2_512: ::prost::alloc::string::String,
    #[prost(string, tag = "20")]
    pub sha3_512: ::prost::alloc::string::String,
    #[prost(string, tag = "21")]
    pub sha3_384: ::prost::alloc::string::String,
    #[prost(string, tag = "22")]
    pub sha3_256: ::prost::alloc::string::String,
    #[prost(string, tag = "23")]
    pub sha3_224: ::prost::alloc::string::String,
    #[prost(string, tag = "32")]
    pub sha2_384: ::prost::alloc::string::String,
}
