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
pub trait PrivateSetIntersectionNode {
    fn submit_set(&mut self, req: super::private_set_intersection::SubmitSetRequest) -> grpc::Result<protobuf::well_known_types::Empty>;
    fn get_intersection(&mut self, req: protobuf::well_known_types::Empty) -> grpc::Result<super::private_set_intersection::GetIntersectionResponse>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch<T: PrivateSetIntersectionNode>(node: &mut T, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
    match method {
        "/oak.examples.private_set_intersection.PrivateSetIntersection/SubmitSet" => grpc::handle_req_rsp(|r| node.submit_set(r), req, writer),
        "/oak.examples.private_set_intersection.PrivateSetIntersection/GetIntersection" => grpc::handle_req_rsp(|r| node.get_intersection(r), req, writer),
        _ => {
            panic!("unknown method name: {}", method);
        }
    };
}
