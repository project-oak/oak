//
// Copyright 2018 The Project Oak Authors
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
    pub mod oak {
        pub use oak::proto::oak::invocation;
        pub use oak_services::proto::oak::log;
        pub mod examples {
            pub mod hello_world {
                include!(concat!(env!("OUT_DIR"), "/oak.examples.hello_world.rs"));
            }
        }
    }
}

pub mod handler;

use anyhow::Context;
use handler::Handler;
use oak::{
    grpc,
    io::{ReceiverExt, Sender, SenderExt},
    CommandHandler,
};
use oak_abi::{label::Label, proto::oak::application::ConfigMap};
use oak_services::proto::oak::log::{LogInit, LogMessage};
use proto::oak::examples::hello_world::Init;

oak::entrypoint_command_handler!(oak_main => Main);

#[derive(Default)]
struct Main;

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: Self::Command) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;

        let router_sender = oak::io::entrypoint_node_create::<Router, _, _>(
            "router",
            &Label::public_untrusted(),
            "app",
            LogInit {
                log_sender: Some(log_sender),
            },
        )?;
        oak::grpc::server::init_with_sender("[::]:8080", router_sender)?;
        Ok(())
    }
}

oak::entrypoint_command_handler_init!(router => Router);

#[derive(Default)]
pub struct Router {
    /// Log sender channel to be sent to every newly created Handler Node.
    log_sender: Sender<LogMessage>,
}

impl oak::WithInit for Router {
    type Init = LogInit;

    fn create(init: Self::Init) -> Self {
        let log_sender = init.log_sender.unwrap();
        oak::logger::init(log_sender.clone(), log::Level::Debug).unwrap();
        Self { log_sender }
    }
}

/// Creates individual Handler Nodes for each client request and assigns client labels to them.
impl CommandHandler for Router {
    type Command = grpc::Invocation;

    fn handle_command(&mut self, invocation: Self::Command) -> anyhow::Result<()> {
        let label = invocation
            .receiver
            .as_ref()
            .context("Couldn't get receiver")?
            .label()
            .context("Couldn't get label")?;

        let translator_sender_option =
            oak::io::entrypoint_node_create::<translator_common::TranslatorEntrypoint, _, _>(
                "translator",
                &label,
                "translator",
                LogInit {
                    log_sender: Some(self.log_sender.clone()),
                },
            )
            .ok();
        if translator_sender_option == None {
            log::warn!("Couldn't create translator node");
        }

        let handler_invocation_sender = oak::io::entrypoint_node_create::<Handler, _, _>(
            "handler",
            &label,
            "app",
            Init {
                log_sender: Some(self.log_sender.clone()),
                translator_sender: translator_sender_option,
            },
        )
        .context("Couldn't create handler node")?;
        let result = handler_invocation_sender
            .send(&invocation)
            .context("Couldn't send invocation to handler node");
        invocation.close()?;
        result
    }
}
