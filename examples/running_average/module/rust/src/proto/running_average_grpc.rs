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
pub trait RunningAverage {
    fn submit_sample(&mut self, req: super::running_average::SubmitSampleRequest) -> grpc::Result<protobuf::well_known_types::Empty>;
    fn get_average(&mut self, req: protobuf::well_known_types::Empty) -> grpc::Result<super::running_average::GetAverageResponse>;
}

// Oak Node gRPC method dispatcher
pub struct Dispatcher<T: RunningAverage>(T);

impl<T: RunningAverage> Dispatcher<T> {
    pub fn new(node: T) -> Dispatcher<T> {
        Dispatcher(node)
    }
}

impl<T: RunningAverage> grpc::OakNode for Dispatcher<T> {
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        match method {
            "/oak.examples.running_average.RunningAverage/SubmitSample" => grpc::handle_req_rsp(|r| self.0.submit_sample(r), req, writer),
            "/oak.examples.running_average.RunningAverage/GetAverage" => grpc::handle_req_rsp(|r| self.0.get_average(r), req, writer),
            _ => {
                panic!("unknown method name: {}", method);
            }
        };
    }
}

// Client interface
pub struct RunningAverageClient(pub oak::grpc::client::Client);

impl RunningAverageClient {
    pub fn submit_sample(&self, req: super::running_average::SubmitSampleRequest) -> grpc::Result<protobuf::well_known_types::Empty> {
        oak::grpc::invoke_grpc_method("/oak.examples.running_average.RunningAverage/SubmitSample", req, &self.0.invocation_sender)
    }
    pub fn get_average(&self, req: protobuf::well_known_types::Empty) -> grpc::Result<super::running_average::GetAverageResponse> {
        oak::grpc::invoke_grpc_method("/oak.examples.running_average.RunningAverage/GetAverage", req, &self.0.invocation_sender)
    }
}
