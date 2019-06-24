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


use protobuf::Message;
use std::io::Write;

// Oak node server interface
pub trait HelloWorldNode {
    fn say_hello(&mut self, req: super::hello_world::HelloRequest) -> super::hello_world::HelloResponse;

    fn lots_of_replies(&mut self, req: super::hello_world::HelloRequest) -> Vec<super::hello_world::HelloResponse>;

    fn lots_of_greetings(&mut self, reqs: Vec<super::hello_world::HelloRequest>) -> super::hello_world::HelloResponse;

    fn bidi_hello(&mut self, reqs: Vec<super::hello_world::HelloRequest>) -> Vec<super::hello_world::HelloResponse>;
}

// Oak node gRPC method dispatcher
pub fn dispatch(node: &mut HelloWorldNode, grpc_method_name: &str, grpc_channel: &mut oak::Channel) {
    match grpc_method_name {
        "/oak.examples.hello_world.HelloWorld/SayHello" => {
            let req = protobuf::parse_from_reader(grpc_channel).unwrap();
            let rsp = node.say_hello(req);
            rsp.write_to_writer(grpc_channel).unwrap();
        }
        "/oak.examples.hello_world.HelloWorld/LotsOfReplies" => {
            let req = protobuf::parse_from_reader(grpc_channel).unwrap();
            let rsps = node.lots_of_replies(req);
            for rsp in rsps {
                rsp.write_to_writer(grpc_channel).unwrap();
            }
        }
        "/oak.examples.hello_world.HelloWorld/LotsOfGreetings" => {
            let mut reqs = vec![];
            loop {
                match protobuf::parse_from_reader(grpc_channel) {
                    Err(_) => break,
                    Ok(req) => reqs.push(req),
                }
            }
            let rsp = node.lots_of_greetings(reqs);
            rsp.write_to_writer(grpc_channel).unwrap();
        }
        "/oak.examples.hello_world.HelloWorld/BidiHello" => {
            let mut reqs = vec![];
            loop {
                match protobuf::parse_from_reader(grpc_channel) {
                    Err(_) => break,
                    Ok(req) => reqs.push(req),
                }
            }
            let rsps = node.bidi_hello(reqs);
            for rsp in rsps {
                rsp.write_to_writer(grpc_channel).unwrap();
            }
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", grpc_method_name).unwrap();
            panic!("unknown method name");
        }
    };
}
