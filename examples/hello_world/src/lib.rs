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
use protobuf::Message;

#[derive(OakNode)]
struct Node;

impl oak::Node for Node {
    fn new() -> Self {
        Node
    }
    fn invoke(&mut self, method_name: &str, grpc: &mut oak::Channel) {
        // TODO: Generate this code via a macro or code generation (e.g. a protoc plugin).
        match method_name {
            "/oak.examples.hello_world.HelloWorld/SayHello" => {
                let mut req;
                {
                    let mut in_stream = protobuf::CodedInputStream::new(grpc);
                    req = proto::hello_world::SayHelloRequest::new();
                    req.merge_from(&mut in_stream)
                        .expect("could not read request");
                }
                let mut res = proto::hello_world::SayHelloResponse::new();
                res.message = format!("HELLO {}!", req.name);
                {
                    let mut out_stream = protobuf::CodedOutputStream::new(grpc);
                    res.write_to(&mut out_stream)
                        .expect("could not write response");
                    out_stream.flush().expect("could not flush");
                }
            }
            _ => {
                panic!("unknown method name");
            }
        };
    }
}
