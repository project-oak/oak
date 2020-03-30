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
use log::error;

// Oak Node server interface
pub trait Translator {
    fn translate(&mut self, req: super::translator::TranslateRequest) -> grpc::Result<super::translator::TranslateResponse>;
}

// Oak Node gRPC method dispatcher
pub struct Dispatcher<T: Translator>(T);

impl<T: Translator> Dispatcher<T> {
    pub fn new(node: T) -> Dispatcher<T> {
        Dispatcher(node)
    }
}

impl<T: Translator> grpc::ServerNode for Dispatcher<T> {
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        match method {
            "/oak.examples.translator.Translator/Translate" => grpc::handle_req_rsp(|r| self.0.translate(r), req, writer),
            _ => {
                error!("unknown method name: {}", method);
            }
        };
    }
}

// Client interface
pub struct TranslatorClient(pub oak::grpc::client::Client);

impl TranslatorClient {
    pub fn translate(&self, req: super::translator::TranslateRequest) -> grpc::Result<super::translator::TranslateResponse> {
        oak::grpc::invoke_grpc_method("/oak.examples.translator.Translator/Translate", &req, Some("type.googleapis.com/oak.examples.translator.TranslateRequest"), &self.0.invocation_sender)
    }
}
