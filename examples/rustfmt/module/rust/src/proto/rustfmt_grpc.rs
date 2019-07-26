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
pub trait FormatServiceNode {
    fn format(&mut self, req: super::rustfmt::FormatRequest) -> GrpcResult<super::rustfmt::FormatResponse>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut dyn FormatServiceNode, method: &str, req: &[u8], out: &mut oak::SendChannelHalf) {
    match method {
        "/oak.examples.rustfmt.FormatService/Format" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            let rsp = node.format(r).unwrap();
            rsp.write_to_writer(out).unwrap();
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", method).unwrap();
            panic!("unknown method name");
        }
    };
}
