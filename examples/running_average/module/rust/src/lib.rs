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

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.running_average.rs"));
}

use anyhow::Context;
use oak::{grpc, Label};
use oak_abi::proto::oak::application::ConfigMap;
use oak_services::proto::oak::log::LogInit;
use proto::{GetAverageResponse, RunningAverage, RunningAverageDispatcher, SubmitSampleRequest};

#[derive(Default)]
struct Main;

oak::entrypoint_command_handler!(oak_main => Main);

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: ConfigMap) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;
        let handler_sender = oak::io::entrypoint_node_create::<Handler, _, _>(
            "handler",
            &Label::public_untrusted(),
            "app",
            LogInit {
                log_sender: Some(log_sender),
            },
        )
        .context("could not create handler node")?;
        oak::grpc::server::init_with_sender("[::]:8080", handler_sender)
            .context("could not create gRPC server pseudo-Node")?;
        Ok(())
    }
}

#[derive(Default)]
struct Handler {
    sum: u64,
    count: u64,
}

oak::entrypoint_command_handler_init!(handler => Handler);
oak::impl_dispatcher!(impl Handler : RunningAverageDispatcher);

impl oak::WithInit for Handler {
    type Init = LogInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self::default()
    }
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
