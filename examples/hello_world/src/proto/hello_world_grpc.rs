// This file is generated. Do not edit
// @generated

// https://github.com/Manishearth/rust-clippy/issues/702
#![allow(unknown_lints)]
#![allow(clippy)]

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

// Oak node server interface
pub trait HelloWorldNode {
    fn say_hello(&mut self, req: super::hello_world::HelloRequest) -> GrpcResult<super::hello_world::HelloResponse>;

    fn lots_of_replies(&mut self, req: super::hello_world::HelloRequest) -> GrpcResult<Vec<super::hello_world::HelloResponse>>;

    fn lots_of_greetings(&mut self, reqs: Vec<super::hello_world::HelloRequest>) -> GrpcResult<super::hello_world::HelloResponse>;

    fn bidi_hello(&mut self, reqs: Vec<super::hello_world::HelloRequest>) -> GrpcResult<Vec<super::hello_world::HelloResponse>>;
}

// Oak node gRPC method dispatcher
pub fn dispatch(node: &mut HelloWorldNode, grpc_method_name: &str, grpc_pair: &mut oak::ChannelPair) {
    match grpc_method_name {
        "/oak.examples.hello_world.HelloWorld/SayHello" => {
            let req = protobuf::parse_from_reader(&mut grpc_pair.receive).unwrap();
            let rsp = node.say_hello(req).unwrap();
            rsp.write_to_writer(&mut grpc_pair.send).unwrap();
        }
        "/oak.examples.hello_world.HelloWorld/LotsOfReplies" => {
            let req = protobuf::parse_from_reader(&mut grpc_pair.receive).unwrap();
            let rsps = node.lots_of_replies(req).unwrap();
            for rsp in rsps {
                rsp.write_to_writer(&mut grpc_pair.send).unwrap();
            }
        }
        "/oak.examples.hello_world.HelloWorld/LotsOfGreetings" => {
            let mut reqs = vec![];
            loop {
                match protobuf::parse_from_reader(&mut grpc_pair.receive) {
                    Err(_) => break,
                    Ok(req) => reqs.push(req),
                }
            }
            let rsp = node.lots_of_greetings(reqs).unwrap();
            rsp.write_to_writer(&mut grpc_pair.send).unwrap();
        }
        "/oak.examples.hello_world.HelloWorld/BidiHello" => {
            let mut reqs = vec![];
            loop {
                match protobuf::parse_from_reader(&mut grpc_pair.receive) {
                    Err(_) => break,
                    Ok(req) => reqs.push(req),
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
