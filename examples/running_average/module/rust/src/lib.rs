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

mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.running_average.rs"));
}
#[cfg(test)]
mod tests;

use oak::grpc;
use proto::{GetAverageResponse, RunningAverage, RunningAverageDispatcher, SubmitSampleRequest};

oak::entrypoint!(oak_main => |in_channel| {
    let dispatcher = RunningAverageDispatcher::new(Node::default());
    oak::run_event_loop(dispatcher, in_channel);
});

oak::entrypoint!(grpc_oak_main => |_in_channel| {
    let dispatcher = RunningAverageDispatcher::new(Node::default());
    let grpc_channel =
        oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
    oak::run_event_loop(dispatcher, grpc_channel);
});

#[derive(Default)]
struct Node {
    sum: u64,
    count: u64,
}

impl RunningAverage for Node {
    fn submit_sample(&mut self, req: SubmitSampleRequest) -> grpc::Result<()> {
        self.sum += req.value;
        self.count += 1;
        Ok(())
    }

    fn get_average(&mut self, _req: ()) -> grpc::Result<GetAverageResponse> {
        let mut res = GetAverageResponse::default();
        res.average = self.sum / self.count;
        Ok(res)
    }
}
