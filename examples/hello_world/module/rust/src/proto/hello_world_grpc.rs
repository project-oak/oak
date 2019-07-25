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
pub fn dispatch(node: &mut dyn HelloWorldNode, grpc_method_name: &str, grpc_pair: &mut oak::ChannelPair) {
    match grpc_method_name {
        "/oak.examples.hello_world.HelloWorld/SayHello" => {
            // If the data fits in 256 bytes it will be read immediately.
            // If not, the vector will be resized and read on second attempt.
            let mut buf = Vec::<u8>::with_capacity(256);
            grpc_pair.receive.read_message(&mut buf).unwrap();
            let req = protobuf::parse_from_bytes(&buf).unwrap();
            let rsp = node.say_hello(req).unwrap();
            rsp.write_to_writer(&mut grpc_pair.send).unwrap();
        }
        "/oak.examples.hello_world.HelloWorld/LotsOfReplies" => {
            // If the data fits in 256 bytes it will be read immediately.
            // If not, the vector will be resized and read on second attempt.
            let mut buf = Vec::<u8>::with_capacity(256);
            grpc_pair.receive.read_message(&mut buf).unwrap();
            let req = protobuf::parse_from_bytes(&buf).unwrap();
            let rsps = node.lots_of_replies(req).unwrap();
            for rsp in rsps {
                rsp.write_to_writer(&mut grpc_pair.send).unwrap();
            }
        }
        "/oak.examples.hello_world.HelloWorld/LotsOfGreetings" => {
            let mut reqs = vec![];
            loop {
                // If the data fits in 256 bytes it will be read immediately.
                // If not, the vector will be resized and read on second attempt.
                let mut buf = Vec::<u8>::with_capacity(256);
                match grpc_pair.receive.read_message(&mut buf) {
                    Err(_) => break,
                    Ok(0) => break,
                    Ok(_size) => reqs.push(protobuf::parse_from_bytes(&buf).unwrap()),
                }
            }
            let rsp = node.lots_of_greetings(reqs).unwrap();
            rsp.write_to_writer(&mut grpc_pair.send).unwrap();
        }
        "/oak.examples.hello_world.HelloWorld/BidiHello" => {
            let mut reqs = vec![];
            loop {
                // If the data fits in 256 bytes it will be read immediately.
                // If not, the vector will be resized and read on second attempt.
                let mut buf = Vec::<u8>::with_capacity(256);
                match grpc_pair.receive.read_message(&mut buf) {
                    Err(_) => break,
                    Ok(0) => break,
                    Ok(_size) => reqs.push(protobuf::parse_from_bytes(&buf).unwrap()),
                }
            }
            let rsps = node.bidi_hello(reqs).unwrap();
            for rsp in rsps {
                rsp.write_to_writer(&mut grpc_pair.send).unwrap();
            }
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", grpc_method_name).unwrap();
            panic!("unknown method name");
        }
    };
}
