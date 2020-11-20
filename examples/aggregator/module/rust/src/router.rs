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

use crate::proto::oak::examples::aggregator::RouterInit;
use oak::io::{forward_invocation, Sender};

/// A node that routes each incoming gRPC invocation to a Handler Node that can handle requests with
/// the label of the incoming request.
///
/// This node never looks at the contents of the invocation messages, only at the labels of its
/// channels, and therefore keeps a public confidentiality label, which also allows it to create
/// further nodes and channels, with more specific labels.
#[derive(Default)]
pub struct Router {
    /// Invocation sender channel half for Handler Node.
    handler_invocation_sender: Sender<oak::grpc::Invocation>,
}

impl oak::CommandHandler for Router {
    type Command = oak::grpc::Invocation;

    fn handle_command(&mut self, command: Self::Command) -> anyhow::Result<()> {
        forward_invocation(command, &self.handler_invocation_sender)
    }
}

impl oak::WithInit for Router {
    type Init = RouterInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        let handler_invocation_sender = init
            .handler_invocation_sender
            .expect("Couldn't receive gRPC invocation sender")
            .sender
            .expect("Empty gRPC invocation sender");
        Self {
            handler_invocation_sender,
        }
    }
}

oak::entrypoint_command_handler_init!(router => Router);
