// This file is generated. Do not edit
// @generated

// https://github.com/rust-lang/rust-clippy/issues/702
#![allow(unknown_lints)]
#![allow(clippy::all)]

#![cfg_attr(rustfmt, rustfmt_skip)]

#![allow(box_pointers)]
#![allow(dead_code)]
#![allow(missing_docs)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(trivial_casts)]
#![allow(unsafe_code)]
#![allow(unused_imports)]
#![allow(unused_results)]


use oak::grpc;
use protobuf::Message;
use std::io::Write;

// Oak Node server interface
pub trait OakABITestService {
    fn run_tests(&mut self, req: super::abitest::ABITestRequest) -> grpc::Result<super::abitest::ABITestResponse>;
    fn unary_method(&mut self, req: super::abitest::GrpcTestRequest) -> grpc::Result<super::abitest::GrpcTestResponse>;
    fn server_streaming_method(&mut self, req: super::abitest::GrpcTestRequest, writer: grpc::ChannelResponseWriter);
    fn client_streaming_method(&mut self, reqs: Vec<super::abitest::GrpcTestRequest>) -> grpc::Result<super::abitest::GrpcTestResponse>;
    fn bidi_streaming_method(&mut self, reqs: Vec<super::abitest::GrpcTestRequest>, writer: grpc::ChannelResponseWriter);
}

// Oak Node gRPC method dispatcher
pub struct Dispatcher<T: OakABITestService>(T);

impl<T: OakABITestService> Dispatcher<T> {
    pub fn new(node: T) -> Dispatcher<T> {
        Dispatcher(node)
    }
}

impl<T: OakABITestService> grpc::ServerNode for Dispatcher<T> {
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        match method {
            "/oak.examples.abitest.OakABITestService/RunTests" => grpc::handle_req_rsp(|r| self.0.run_tests(r), req, writer),
            "/oak.examples.abitest.OakABITestService/UnaryMethod" => grpc::handle_req_rsp(|r| self.0.unary_method(r), req, writer),
            "/oak.examples.abitest.OakABITestService/ServerStreamingMethod" => grpc::handle_req_stream(|r, w| self.0.server_streaming_method(r, w), req, writer),
            "/oak.examples.abitest.OakABITestService/ClientStreamingMethod" => grpc::handle_stream_rsp(|rr| self.0.client_streaming_method(rr), req, writer),
            "/oak.examples.abitest.OakABITestService/BidiStreamingMethod" => grpc::handle_stream_stream(|rr, w| self.0.bidi_streaming_method(rr, w), req, writer),
            _ => {
                panic!("unknown method name: {}", method);
            }
        };
    }
}

// Client interface
pub struct OakABITestServiceClient(pub oak::grpc::client::Client);

impl OakABITestServiceClient {
    pub fn run_tests(&self, req: super::abitest::ABITestRequest) -> grpc::Result<super::abitest::ABITestResponse> {
        oak::grpc::invoke_grpc_method("/oak.examples.abitest.OakABITestService/RunTests", req, Some("type.googleapis.com/oak.examples.abitest.ABITestRequest"), &self.0.invocation_sender)
    }
    pub fn unary_method(&self, req: super::abitest::GrpcTestRequest) -> grpc::Result<super::abitest::GrpcTestResponse> {
        oak::grpc::invoke_grpc_method("/oak.examples.abitest.OakABITestService/UnaryMethod", req, Some("type.googleapis.com/oak.examples.abitest.GrpcTestRequest"), &self.0.invocation_sender)
    }
    pub fn server_streaming_method(&self, req: super::abitest::GrpcTestRequest) -> grpc::Result<oak::io::Receiver<grpc::GrpcResponse>> {
        oak::grpc::invoke_grpc_method_stream("/oak.examples.abitest.OakABITestService/ServerStreamingMethod", req, Some("type.googleapis.com/oak.examples.abitest.GrpcTestRequest"), &self.0.invocation_sender)
    }
}
