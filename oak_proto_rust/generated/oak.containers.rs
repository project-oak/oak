/// As images can be large (hundreds of megabytes), the launcher chunks up the
/// response into smaller pieces to respect proto/gRPC limits. The image needs to
/// be reassembled in the stage1 or the orchestrator.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GetImageResponse {
    #[prost(bytes = "vec", tag = "1")]
    pub image_chunk: ::prost::alloc::vec::Vec<u8>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GetApplicationConfigResponse {
    /// Arbitrary config that the container can retrieve from the orchestrator.
    /// Included in the attestation measurements conducted by the orchestrator.
    #[prost(bytes = "vec", tag = "1")]
    pub config: ::prost::alloc::vec::Vec<u8>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SendAttestationEvidenceRequest {
    #[prost(message, optional, tag = "2")]
    pub dice_evidence: ::core::option::Option<super::attestation::v1::Evidence>,
}
