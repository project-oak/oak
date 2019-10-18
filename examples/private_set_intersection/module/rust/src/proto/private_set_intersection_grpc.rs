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


use oak::grpc;
use protobuf::Message;
use std::io::Write;

// Oak Node server interface
pub trait PrivateSetIntersectionNode {
    fn submit_set(&mut self, req: super::private_set_intersection::SubmitSetRequest) -> grpc::Result<()>;

    fn get_intersection(&mut self) -> grpc::Result<super::private_set_intersection::GetIntersectionResponse>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut dyn PrivateSetIntersectionNode, method: &str, req: &[u8], mut writer: grpc::ChannelResponseWriter) {
    match method {
        "/oak.examples.private_set_intersection.PrivateSetIntersection/SubmitSet" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            match node.submit_set(r) {
                Ok(_) => writer.write_empty(grpc::WriteMode::Close),
                Err(status) => writer.close(Err(status)),
            }
        }
        "/oak.examples.private_set_intersection.PrivateSetIntersection/GetIntersection" => {
            match node.get_intersection() {
                Ok(rsp) => writer.write(rsp, grpc::WriteMode::Close),
                Err(status) => writer.close(Err(status)),
            }
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", method).unwrap();
            panic!("unknown method name");
        }
    };
}
