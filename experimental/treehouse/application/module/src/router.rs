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

use crate::{handler::Handler, proto::oak::examples::treehouse::TreehouseInit};
use anyhow::Context;
use oak::{
    grpc,
    io::{ReceiverExt, SenderExt},
    CommandHandler,
};

#[derive(Default)]
pub struct Router {
    init: TreehouseInit,
}

impl oak::WithInit for Router {
    type Init = TreehouseInit;

    fn create(init: Self::Init) -> Self {
        Self { init }
    }
}

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
        handler_invocation_sender
            .send(&invocation)
            .context("Couldn't send invocation to handler node")
    }
}

oak::entrypoint_command_handler_init!(router => Router);
