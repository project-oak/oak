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
pub trait FormatService {
    fn format(&mut self, req: super::rustfmt::FormatRequest) -> grpc::Result<super::rustfmt::FormatResponse>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch<T: FormatService>(node: &mut T, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
    match method {
        "/oak.examples.rustfmt.FormatService/Format" => grpc::handle_req_rsp(|r| node.format(r), req, writer),
        _ => {
            panic!("unknown method name: {}", method);
        }
    };
}

// Client interface
pub struct FormatServiceClient(pub oak::grpc::client::Client);

impl FormatServiceClient {
    pub fn format(&self, req: super::rustfmt::FormatRequest) -> grpc::Result<super::rustfmt::FormatResponse> {
        oak::grpc::invoke_grpc_method("/oak.examples.rustfmt.FormatService/Format", req, &self.0.invocation_sender)
    }
}
