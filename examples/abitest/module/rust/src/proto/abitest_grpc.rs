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
pub trait OakABITestServiceNode {
    fn run_tests(&mut self, req: super::abitest::ABITestRequest) -> grpc::Result<super::abitest::ABITestResponse>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut dyn OakABITestServiceNode, method: &str, req: &[u8], mut writer: grpc::ChannelResponseWriter) {
    match method {
        "/oak.examples.abitest.OakABITestService/RunTests" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            match node.run_tests(r) {
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
