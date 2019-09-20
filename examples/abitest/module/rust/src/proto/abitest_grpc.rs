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
pub trait ExampleServiceNode {
    fn example_method(&mut self, req: super::abitest::ExampleRequest) -> GrpcResult<super::abitest::ExampleResponse>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut dyn ExampleServiceNode, method: &str, req: &[u8], out: &mut oak::SendChannelHalf) {
    match method {
        "/oak.examples.abitest.ExampleService/ExampleMethod" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            let mut result = oak::proto::grpc_encap::GrpcResponse::new();
            match node.example_method(r) {
                Ok(rsp) => {
                    let mut any = protobuf::well_known_types::Any::new();
                    rsp.write_to_writer(&mut any.value).unwrap();
                    result.set_rsp_msg(any);
                }
                Err(status) => result.set_status(status),
            }
            result.set_last(true);
            result.write_to_writer(out).unwrap();
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", method).unwrap();
            panic!("unknown method name");
        }
    };
}
