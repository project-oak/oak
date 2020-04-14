// Protocol buffer encoding to hold additional metadata that accompanies a gRPC
// message exchange.  This is normally encoded using various HTTP2 features
// (https://github.com/grpc/grpc/blob/master/doc/PROTOCOL-HTTP2.md) but to avoid
// the need for a full HTTP2 implementation inside each Oak Node, we define a
// simplified envelope format that includes the relevant details.

#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GrpcRequest {
    #[prost(string, tag="1")]
    pub method_name: std::string::String,
    /// The body of the request. Usually a serialized protobuf message.
    /// The message type is deduced from the `method_name` field.
    #[prost(bytes, tag="2")]
    pub req_msg: std::vec::Vec<u8>,
    #[prost(bool, tag="3")]
    pub last: bool,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GrpcResponse {
    /// The body of the response. Usually a serialized protobuf message.
    /// The message type is deduced from the `method_name` field of the request.
    #[prost(bytes, tag="1")]
    pub rsp_msg: std::vec::Vec<u8>,
    #[prost(message, optional, tag="2")]
    pub status: ::std::option::Option<super::super::google::rpc::Status>,
    /// The last field indicates that this is definitely the final response for a
    /// method invocation. However, the converse is not true: the final response may
    /// have last=false, and the completion of the method invocation will then be
    /// indicated by the closure of the response channel.
    #[prost(bool, tag="3")]
    pub last: bool,
}
