// This file is generated. Do not edit
// @generated

// https://github.com/Manishearth/rust-clippy/issues/702
#![allow(unknown_lints)]
#![allow(clippy)]

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

// Oak node server interface
pub trait PrivateSetIntersectionNode {
    fn submit_set(&mut self, req: super::private_set_intersection::SubmitSetRequest) -> GrpcResult<()>;

    fn get_intersection(&mut self) -> GrpcResult<super::private_set_intersection::GetIntersectionResponse>;
}

// Oak node gRPC method dispatcher
pub fn dispatch(node: &mut PrivateSetIntersectionNode, grpc_method_name: &str, grpc_pair: &mut oak::ChannelPair) {
    match grpc_method_name {
        "/oak.examples.private_set_intersection.PrivateSetIntersection/SubmitSet" => {
            let req = protobuf::parse_from_reader(&mut grpc_pair.receive).unwrap();
            node.submit_set(req).unwrap();
        }
        "/oak.examples.private_set_intersection.PrivateSetIntersection/GetIntersection" => {
            let rsp = node.get_intersection().unwrap();
            rsp.write_to_writer(&mut grpc_pair.send).unwrap();
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", grpc_method_name).unwrap();
            panic!("unknown method name");
        }
    };
}
