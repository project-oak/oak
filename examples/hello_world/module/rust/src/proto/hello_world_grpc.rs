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
pub trait HelloWorld {
    fn say_hello(&mut self, req: super::hello_world::HelloRequest) -> grpc::Result<super::hello_world::HelloResponse>;
    fn lots_of_replies(&mut self, req: super::hello_world::HelloRequest, writer: grpc::ChannelResponseWriter);
    fn lots_of_greetings(&mut self, reqs: Vec<super::hello_world::HelloRequest>) -> grpc::Result<super::hello_world::HelloResponse>;
    fn bidi_hello(&mut self, reqs: Vec<super::hello_world::HelloRequest>, writer: grpc::ChannelResponseWriter);
}

// Oak Node gRPC method dispatcher
pub struct Dispatcher<T: HelloWorld>(T);

impl<T: HelloWorld> Dispatcher<T> {
    pub fn new(node: T) -> Dispatcher<T> {
        Dispatcher(node)
    }
}

impl<T: HelloWorld> grpc::ServerNode for Dispatcher<T> {
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        match method {
            "/oak.examples.hello_world.HelloWorld/SayHello" => grpc::handle_req_rsp(|r| self.0.say_hello(r), req, writer),
            "/oak.examples.hello_world.HelloWorld/LotsOfReplies" => grpc::handle_req_stream(|r, w| self.0.lots_of_replies(r, w), req, writer),
            "/oak.examples.hello_world.HelloWorld/LotsOfGreetings" => grpc::handle_stream_rsp(|rr| self.0.lots_of_greetings(rr), req, writer),
            "/oak.examples.hello_world.HelloWorld/BidiHello" => grpc::handle_stream_stream(|rr, w| self.0.bidi_hello(rr, w), req, writer),
            _ => {
                panic!("unknown method name: {}", method);
            }
        };
    }
}

// Client interface
pub struct HelloWorldClient(pub oak::grpc::client::Client);

impl HelloWorldClient {
    pub fn say_hello(&self, req: super::hello_world::HelloRequest) -> grpc::Result<super::hello_world::HelloResponse> {
        oak::grpc::invoke_grpc_method("/oak.examples.hello_world.HelloWorld/SayHello", req, &self.0.invocation_sender)
    }
    pub fn lots_of_replies(&self, req: super::hello_world::HelloRequest) -> grpc::Result<oak::io::Receiver<grpc::GrpcResponse>> {
        oak::grpc::invoke_grpc_method_stream("/oak.examples.hello_world.HelloWorld/LotsOfReplies", req, &self.0.invocation_sender)
    }
}
