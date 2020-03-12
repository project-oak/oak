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
pub trait PrivateSetIntersection {
    fn submit_set(&mut self, req: super::private_set_intersection::SubmitSetRequest) -> grpc::Result<protobuf::well_known_types::Empty>;
    fn get_intersection(&mut self, req: protobuf::well_known_types::Empty) -> grpc::Result<super::private_set_intersection::GetIntersectionResponse>;
}

// Oak Node gRPC method dispatcher
pub struct Dispatcher<T: PrivateSetIntersection>(T);

impl<T: PrivateSetIntersection> Dispatcher<T> {
    pub fn new(node: T) -> Dispatcher<T> {
        Dispatcher(node)
    }
}

impl<T: PrivateSetIntersection> grpc::ServerNode for Dispatcher<T> {
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        match method {
            "/oak.examples.private_set_intersection.PrivateSetIntersection/SubmitSet" => grpc::handle_req_rsp(|r| self.0.submit_set(r), req, writer),
            "/oak.examples.private_set_intersection.PrivateSetIntersection/GetIntersection" => grpc::handle_req_rsp(|r| self.0.get_intersection(r), req, writer),
            _ => {
                panic!("unknown method name: {}", method);
            }
        };
    }
}

// Client interface
pub struct PrivateSetIntersectionClient(pub oak::grpc::client::Client);

impl PrivateSetIntersectionClient {
    pub fn submit_set(&self, req: super::private_set_intersection::SubmitSetRequest) -> grpc::Result<protobuf::well_known_types::Empty> {
        oak::grpc::invoke_grpc_method("/oak.examples.private_set_intersection.PrivateSetIntersection/SubmitSet", &req, Some("type.googleapis.com/oak.examples.private_set_intersection.SubmitSetRequest"), &self.0.invocation_sender)
    }
    pub fn get_intersection(&self, req: protobuf::well_known_types::Empty) -> grpc::Result<super::private_set_intersection::GetIntersectionResponse> {
        oak::grpc::invoke_grpc_method("/oak.examples.private_set_intersection.PrivateSetIntersection/GetIntersection", &req, Some("type.googleapis.com/google.protobuf.Empty"), &self.0.invocation_sender)
    }
}
