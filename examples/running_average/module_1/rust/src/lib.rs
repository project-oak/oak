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

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.running_average.rs"));
}

use oak::grpc;
use proto::{GetAverageResponse, RunningAverage, RunningAverageDispatcher, SubmitSampleRequest};

oak::entrypoint_command_handler!(handler => Handler);

#[derive(Default)]
pub struct Handler {
    sum: u64,
    count: u64,
}

impl RunningAverage for Handler {
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

oak::impl_dispatcher!(impl Handler : RunningAverageDispatcher);
