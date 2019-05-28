//
// Copyright 2019 The Project Oak Authors
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

//! Private Set Intersection example for Project Oak.
//!
//! Clients invoke the module by providing their own private set, and the module keeps track of the
//! intersection of all the provided sets from all the clients that have interacted with it.
//!
//! The (common) intersection can then be retrieved by each client by a separate invocation.
//!
//! TODO: Limit number of clients / sets that may contribute to the intersection.
//! TODO: Consider stopping accepting contributions after the first client retrieves the
//! intersection.

extern crate oak;
extern crate oak_derive;
extern crate protobuf;

mod proto;

use oak_derive::OakNode;
use protobuf::Message;
use std::collections::HashSet;
use std::io::Write;

#[derive(Default, OakNode)]
struct Node {
    values: Option<HashSet<String>>,
}

impl oak::Node for Node {
    fn new() -> Self {
        Node::default()
    }
    fn invoke(&mut self, grpc_method_name: &str, grpc_channel: &mut oak::Channel) {
        let mut logging_channel = oak::logging_channel();
        // TODO: Generate this code via a macro or code generation (e.g. a protoc plugin).
        match grpc_method_name {
            "/oak.examples.private_set_intersection.PrivateSetIntersection/SubmitSet" => {
                let mut in_stream = protobuf::CodedInputStream::new(grpc_channel);
                let mut req = proto::private_set_intersection::SubmitSetRequest::new();
                req.merge_from(&mut in_stream)
                    .expect("could not read request");
                let set = req.values.iter().cloned().collect::<HashSet<_>>();
                let next = match self.values {
                    Some(ref previous) => previous.intersection(&set).cloned().collect(),
                    None => set,
                };
                self.values = Some(next);
            }
            "/oak.examples.private_set_intersection.PrivateSetIntersection/GetIntersection" => {
                let mut res = proto::private_set_intersection::GetIntersectionResponse::new();
                if let Some(ref set) = self.values {
                    res.values = set.iter().cloned().collect();
                };
                let mut out_stream = protobuf::CodedOutputStream::new(grpc_channel);
                res.write_to(&mut out_stream)
                    .expect("could not write response");
                out_stream.flush().expect("could not flush");
            }
            _ => {
                writeln!(logging_channel, "unknown method name: {}", grpc_method_name).unwrap();
                panic!("unknown method name");
            }
        };
    }
}
