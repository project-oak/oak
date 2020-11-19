//
// Copyright 2020 The Project Oak Authors
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

use crate::{
    handler::Handler,
    proto::oak::examples::trusted_database::{PointOfInterestMap, TrustedDatabaseInit},
};
use anyhow::Context;
use oak::{
    grpc,
    io::{ReceiverExt, Sender},
    CommandHandler,
};
use oak_services::proto::oak::log::LogMessage;

/// Oak Router Node that contains an in-memory database.
#[derive(Default)]
pub struct Router {
    log_sender: Sender<LogMessage>,
    points_of_interest: PointOfInterestMap,
}

impl oak::WithInit for Router {
    type Init = TrustedDatabaseInit;

    fn create(init: Self::Init) -> Self {
        let log_sender = init.log_sender.unwrap();
        oak::logger::init(log_sender.clone(), log::Level::Debug).unwrap();
        let points_of_interest = init.points_of_interest.expect("Couldn't receive database");
        Self {
            log_sender,
            points_of_interest,
        }
    }
}

impl CommandHandler for Router {
    type Command = grpc::Invocation;

    fn handle_command(&mut self, invocation: Self::Command) -> anyhow::Result<()> {
        let label = invocation
            .receiver
            .context("Couldn't get receiver")?
            .label()
            .context("Couldn't get label")?;
        let init = TrustedDatabaseInit {
            log_sender: Some(self.log_sender.clone()),
            points_of_interest: Some(self.points_of_interest.clone()),
        };
        oak::io::entrypoint_node_create::<Handler, _, _>("handler", &label, "app", init)
            .context("Couldn't create handler node")?;
        Ok(())
    }
}

oak::entrypoint_command_handler_init!(router => Router);
