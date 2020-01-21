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

mod proto;

use oak::grpc;
use oak::grpc::OakGrpcServerNode;
use oak_derive::OakGrpcEntrypoint;
use proto::running_average::{GetAverageResponse, SubmitSampleRequest};
use proto::running_average_grpc::{dispatch, RunningAverageNode};
use protobuf::well_known_types::Empty;
use protobuf::ProtobufEnum;

#[derive(Default, OakGrpcEntrypoint)]
struct Node {
    sum: u64,
    count: u64,
}

impl OakGrpcServerNode for Node {
    fn new() -> Self {
        Node::default()
    }
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

impl RunningAverageNode for Node {
    fn submit_sample(&mut self, req: SubmitSampleRequest) -> grpc::Result<Empty> {
        self.sum += req.value;
        self.count += 1;
        Ok(Empty::new())
    }

    fn get_average(&mut self, _req: Empty) -> grpc::Result<GetAverageResponse> {
        let mut res = GetAverageResponse::new();
        res.average = self.sum / self.count;
        Ok(res)
    }
}
