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
use proto::hello_world_grpc::{dispatch, HelloWorldNode};

#[derive(OakNode)]
struct Node;

impl oak::Node for Node {
    fn new() -> Self {
        oak_log::init(log::Level::Debug).unwrap();
        Node
    }
    fn invoke(&mut self, grpc_method_name: &str, grpc_pair: &mut oak::ChannelPair) {
        dispatch(self, grpc_method_name, grpc_pair)
    }
}

impl HelloWorldNode for Node {
    fn say_hello(&mut self, req: HelloRequest) -> HelloResponse {
        info!("Say hello to {}", req.greeting);
        let mut res = HelloResponse::new();
        res.reply = format!("HELLO {}!", req.greeting);
        res
    }

    fn lots_of_replies(&mut self, req: HelloRequest) -> Vec<HelloResponse> {
        info!("Say hello to {}", req.greeting);
        let mut res1 = HelloResponse::new();
        res1.reply = format!("HELLO {}!", req.greeting);
        let mut res2 = HelloResponse::new();
        res2.reply = format!("BONJOUR {}!", req.greeting);
        vec![res1, res2]
    }

    fn lots_of_greetings(&mut self, reqs: Vec<HelloRequest>) -> HelloResponse {
        info!("Say hello");
        let mut msg = String::new();
        msg.push_str("Hello ");
        msg.push_str(&recipients(&reqs));
        let mut res = HelloResponse::new();
        res.reply = msg;
        res
    }

    fn bidi_hello(&mut self, reqs: Vec<HelloRequest>) -> Vec<HelloResponse> {
        info!("Say hello");
        let msg = recipients(&reqs);
        let mut res1 = HelloResponse::new();
        res1.reply = format!("HELLO {}!", msg);
        let mut res2 = HelloResponse::new();
        res2.reply = format!("BONJOUR {}!", msg);
        vec![res1, res2]
    }
}

fn recipients(reqs: &Vec<HelloRequest>) -> String {
    let mut result = String::new();
    for (i, req) in reqs.iter().enumerate() {
        if i > 0 {
            result.push_str(", ");
        }
        result.push_str(&req.greeting);
    }
    result
}
