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

use crate::{handler::Handler, proto::oak::examples::trusted_database::TrustedDatabaseInit};
use anyhow::Context;
use oak::{
    grpc,
    io::{ReceiverExt, SenderExt},
    CommandHandler,
};

/// Oak Router Node that contains an in-memory database (saved in the `init`).
#[derive(Default)]
pub struct Router {
    /// Init message to be sent to every newly created Handler Node.
    init: TrustedDatabaseInit,
}

impl oak::WithInit for Router {
    type Init = TrustedDatabaseInit;

    fn create(init: Self::Init) -> Self {
        Self { init }
    }
}

/// Processes client requests and creates individual Handler Nodes.
/// Each newly created Handler Node receives a copy of the database stored in [`Router::init`].
impl CommandHandler for Router {
    type Command = grpc::Invocation;

    fn handle_command(&mut self, invocation: Self::Command) -> anyhow::Result<()> {
        let label = invocation
            .receiver
            .as_ref()
            .context("Couldn't get receiver")?
            .label()
            .context("Couldn't get label")?;
        let handler_invocation_sender = oak::io::entrypoint_node_create::<Handler, _, _>(
            "handler",
            &label,
            "app",
            self.init.clone(),
        )
        .context("Couldn't create handler node")?;
        let result = handler_invocation_sender
            .send(&invocation)
            .context("Couldn't send invocation to handler node");
        invocation.close()?;
        result
    }
}

oak::entrypoint_command_handler_init!(router => Router);
