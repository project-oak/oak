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
pub trait HelloWorldNode {
    fn say_hello(&mut self, req: super::hello_world::HelloRequest) -> GrpcResult<super::hello_world::HelloResponse>;

    fn lots_of_replies(&mut self, req: super::hello_world::HelloRequest) -> GrpcResult<Vec<super::hello_world::HelloResponse>>;

    fn lots_of_greetings(&mut self, reqs: Vec<super::hello_world::HelloRequest>) -> GrpcResult<super::hello_world::HelloResponse>;

    fn bidi_hello(&mut self, reqs: Vec<super::hello_world::HelloRequest>) -> GrpcResult<Vec<super::hello_world::HelloResponse>>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut dyn HelloWorldNode, method: &str, req: &[u8], out: &mut oak::SendChannelHalf) {
    match method {
        "/oak.examples.hello_world.HelloWorld/SayHello" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            let rsp = node.say_hello(r).unwrap();
            rsp.write_to_writer(out).unwrap();
        }
        "/oak.examples.hello_world.HelloWorld/LotsOfReplies" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            let rsps = node.lots_of_replies(r).unwrap();
            for rsp in rsps {
                rsp.write_to_writer(out).unwrap();
            }
        }
        "/oak.examples.hello_world.HelloWorld/LotsOfGreetings" => {
            let rr = vec![protobuf::parse_from_bytes(&req).unwrap()];
            let rsp = node.lots_of_greetings(rr).unwrap();
            rsp.write_to_writer(out).unwrap();
        }
        "/oak.examples.hello_world.HelloWorld/BidiHello" => {
            let rr = vec![protobuf::parse_from_bytes(&req).unwrap()];
            let rsps = node.bidi_hello(rr).unwrap();
            for rsp in rsps {
                rsp.write_to_writer(out).unwrap();
            }
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", method).unwrap();
            panic!("unknown method name");
        }
    };
}
