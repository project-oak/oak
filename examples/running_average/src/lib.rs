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

//! Running average example for Project Oak.
//!
//! This shows how an Oak Mode can maintain some internal state across multiple invocations.
//!
//! Clients invoke the module by providing a string representation of a non-negative number
//! expressed in base 10, and get back a string representation of the accumulated average value up
//! to and including the value provided in the request.

extern crate oak;
extern crate oak_derive;
extern crate protobuf;

mod proto;

use oak_derive::OakNode;
use protobuf::Message;

#[derive(Default, OakNode)]
struct Node {
    sum: u64,
    count: u64,
}

impl oak::Node for Node {
    fn new() -> Self {
        Node::default()
    }
    fn invoke(&mut self, method_name: &str, request: &mut oak::Reader, response: &mut oak::Writer) {
        // TODO: Generate this code via a macro or code generation (e.g. a protoc plugin).
        match method_name {
            "/oak.examples.running_average.RunningAverage/SubmitSample" => {
                let mut in_stream = protobuf::CodedInputStream::new(request);
                let mut req = proto::running_average::SubmitSampleRequest::new();
                req.merge_from(&mut in_stream)
                    .expect("could not read request");
                self.sum += req.value;
                self.count += 1;
            }
            "/oak.examples.running_average.RunningAverage/GetAverage" => {
                let mut res = proto::running_average::GetAverageResponse::new();
                let mut out_stream = protobuf::CodedOutputStream::new(response);
                res.average = self.sum / self.count;
                res.write_to(&mut out_stream)
                    .expect("could not write response");
                out_stream.flush().expect("could not flush");
            }
            _ => {
                panic!("unknown method name");
            }
        };
    }
}
