// This file is generated. Do not edit
// @generated

// https://github.com/Manishearth/rust-clippy/issues/702
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


use oak::GrpcResult;
use protobuf::Message;
use std::io::Write;

// Oak Node server interface
pub trait PrivateSetIntersectionNode {
    fn submit_set(&mut self, req: super::private_set_intersection::SubmitSetRequest) -> GrpcResult<()>;

    fn get_intersection(&mut self) -> GrpcResult<super::private_set_intersection::GetIntersectionResponse>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut dyn PrivateSetIntersectionNode, method: &str, req: &[u8], out: &mut oak::SendChannelHalf) {
    match method {
        "/oak.examples.private_set_intersection.PrivateSetIntersection/SubmitSet" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            node.submit_set(r).unwrap();
        }
        "/oak.examples.private_set_intersection.PrivateSetIntersection/GetIntersection" => {
            let rsp = node.get_intersection().unwrap();
            rsp.write_to_writer(out).unwrap();
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", method).unwrap();
            panic!("unknown method name");
        }
    };
}
