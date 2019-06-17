//
// Copyright 2018 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

#[macro_use]
extern crate log;
extern crate oak;
extern crate oak_derive;
extern crate oak_log;
extern crate protobuf;

mod proto;

use oak_derive::OakNode;
use proto::hello_world::{HelloRequest, HelloResponse};
use protobuf::Message;
use std::io::Write;

#[derive(OakNode)]
struct Node;

// TODO: Generate this code via a macro or code generation (e.g. a protoc plugin).
trait HelloWorldNode {
    fn say_hello(&self, req: &HelloRequest) -> HelloResponse;
}

// TODO: Generate this code via a macro or code generation (e.g. a protoc plugin).
impl oak::Node for Node {
    fn new() -> Self {
        oak_log::init(log::Level::Debug).unwrap();
        Node
    }
    fn invoke(&mut self, grpc_method_name: &str, grpc_channel: &mut oak::Channel) {
        let mut logging_channel = oak::logging_channel();
        match grpc_method_name {
            "/oak.examples.hello_world.HelloWorld/SayHello" => {
                let req = protobuf::parse_from_reader(grpc_channel).unwrap();
                let res = (self as &mut HelloWorldNode).say_hello(&req);
                res.write_to_writer(grpc_channel).unwrap();
            }
            _ => {
                writeln!(logging_channel, "unknown method name: {}", grpc_method_name).unwrap();
                panic!("unknown method name");
            }
        };
    }
}

// TODO: Generate parts of this code via a macro or code generation (e.g. a protoc plugin).
impl HelloWorldNode for Node {
    fn say_hello(&self, req: &HelloRequest) -> HelloResponse {
        let mut res = HelloResponse::new();
        info!("Say hello to {}", req.greeting);
        res.reply = format!("HELLO {}!", req.greeting);
        res
    }
}

