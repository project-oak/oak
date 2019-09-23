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
pub trait FormatServiceNode {
    fn format(&mut self, req: super::rustfmt::FormatRequest) -> grpc::Result<super::rustfmt::FormatResponse>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut dyn FormatServiceNode, method: &str, req: &[u8], out: &mut oak::WriteHandle) {
    match method {
        "/oak.examples.rustfmt.FormatService/Format" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            let mut result = oak::proto::grpc_encap::GrpcResponse::new();
            match node.format(r) {
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
