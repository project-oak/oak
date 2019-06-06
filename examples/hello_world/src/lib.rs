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

extern crate oak;
extern crate oak_derive;
extern crate protobuf;

mod proto;

use oak_derive::OakNode;
use proto::hello_world::{SayHelloRequest, SayHelloResponse};
use protobuf::Message;
use std::io::Write;

#[derive(OakNode)]
struct Node;

impl Node {
    fn say_hello(&self, req: &SayHelloRequest) -> SayHelloResponse {
        let mut res = SayHelloResponse::new();
        res.message = format!("HELLO {}!", req.name);
        res
    }
}

impl oak::Node for Node {
    fn new() -> Self {
        Node
    }
    fn invoke(&mut self, grpc_method_name: &str, grpc_channel: &mut oak::Channel) {
        let mut logging_channel = oak::logging_channel();
        // TODO: Generate this code via a macro or code generation (e.g. a protoc plugin).
        match grpc_method_name {
            "/oak.examples.hello_world.HelloWorld/SayHello" => {
                let req = protobuf::parse_from_reader(grpc_channel).unwrap();
                let res = self.say_hello(&req);
                res.write_to_writer(grpc_channel).unwrap();
            }
            _ => {
                writeln!(logging_channel, "unknown method name: {}", grpc_method_name).unwrap();
                panic!("unknown method name");
            }
        };
    }
}
