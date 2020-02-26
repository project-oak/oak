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
}

// Oak Node gRPC method dispatcher
pub struct Dispatcher<T: OakABITestService>(T);

impl<T: OakABITestService> Dispatcher<T> {
    pub fn new(node: T) -> Dispatcher<T> {
        Dispatcher(node)
    }
}

impl<T: OakABITestService> grpc::OakNode for Dispatcher<T> {
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        match method {
            "/oak.examples.abitest.OakABITestService/RunTests" => grpc::handle_req_rsp(|r| self.0.run_tests(r), req, writer),
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
        oak::grpc::invoke_grpc_method("/oak.examples.abitest.OakABITestService/RunTests", req, &self.0.invocation_sender)
    }
}
