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
pub trait Aggregator {
    fn submit_sample(&mut self, req: super::aggregator_test::Vector) -> grpc::Result<protobuf::well_known_types::Empty>;
    fn get_current_value(&mut self, req: protobuf::well_known_types::Empty) -> grpc::Result<super::aggregator_test::Vector>;
}

// Oak Node gRPC method dispatcher
pub struct Dispatcher<T: Aggregator>(T);

impl<T: Aggregator> Dispatcher<T> {
    pub fn new(node: T) -> Dispatcher<T> {
        Dispatcher(node)
    }
}

impl<T: Aggregator> grpc::ServerNode for Dispatcher<T> {
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        match method {
            "/oak.examples.aggregator_test.Aggregator/SubmitSample" => grpc::handle_req_rsp(|r| self.0.submit_sample(r), req, writer),
            "/oak.examples.aggregator_test.Aggregator/GetCurrentValue" => grpc::handle_req_rsp(|r| self.0.get_current_value(r), req, writer),
            _ => {
                panic!("unknown method name: {}", method);
            }
        };
    }
}

// Client interface
pub struct AggregatorClient(pub oak::grpc::client::Client);

impl AggregatorClient {
    pub fn submit_sample(&self, req: super::aggregator_test::Vector) -> grpc::Result<protobuf::well_known_types::Empty> {
        oak::grpc::invoke_grpc_method("/oak.examples.aggregator_test.Aggregator/SubmitSample", &req, Some("type.googleapis.com/oak.examples.aggregator_test.Vector"), &self.0.invocation_sender)
    }
    pub fn get_current_value(&self, req: protobuf::well_known_types::Empty) -> grpc::Result<super::aggregator_test::Vector> {
        oak::grpc::invoke_grpc_method("/oak.examples.aggregator_test.Aggregator/GetCurrentValue", &req, Some("type.googleapis.com/google.protobuf.Empty"), &self.0.invocation_sender)
    }
}
