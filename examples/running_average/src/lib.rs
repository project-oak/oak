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
use proto::running_average::{GetAverageResponse, SubmitSampleRequest};
use proto::running_average_grpc::{dispatch, RunningAverageNode};

#[derive(Default, OakNode)]
struct Node {
    sum: u64,
    count: u64,
}

impl oak::Node for Node {
    fn new() -> Self {
        Node::default()
    }
    fn invoke(&mut self, grpc_method_name: &str, grpc_channel: &mut oak::Channel) {
        dispatch(self, grpc_method_name, grpc_channel)
    }
}

impl RunningAverageNode for Node {
    fn submit_sample(&mut self, req: SubmitSampleRequest) {
        self.sum += req.value;
        self.count += 1;
    }

    fn get_average(&mut self) -> GetAverageResponse {
        let mut res = GetAverageResponse::new();
        res.average = self.sum / self.count;
        res
    }
}
