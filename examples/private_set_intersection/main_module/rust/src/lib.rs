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

use anyhow::Context;
use oak::{
    io::{forward_invocation, Sender},
    Label,
};
use oak_abi::{
    label::{confidentiality_label, web_assembly_module_signature_tag},
    proto::oak::application::ConfigMap,
};
use oak_services::proto::oak::log::LogInit;
use private_set_intersection_handler::Handler;

// Base64 encoded Ed25519 public key corresponding to Wasm module signature.
// Originated from `/examples/keys/ed25519/test.pub`.
const PUBLIC_KEY_BASE64: &str = "MCowBQYDK2VwAyEAf41SClNtR4i46v2Tuh1fQLbt/ZqRr1lENajCW92jyP4=";

oak::entrypoint_command_handler!(oak_main => Main);

#[derive(Default)]
struct Main;

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: ConfigMap) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;
        let router_command_sender = oak::io::entrypoint_node_create::<Router, _, _>(
            "router",
            &Label::public_untrusted(),
            "app",
            LogInit {
                log_sender: Some(log_sender),
            },
        )
        .context("Couldn't create router node")?;

        oak::grpc::server::init_with_sender("[::]:8080", router_command_sender)
            .context("Couldn't create gRPC server pseudo-Node")?;
        Ok(())
    }
}

oak::entrypoint_command_handler_init!(router => Router);

struct Router {
    /// Invocation sender channel half for Handler Node.
    handler_command_sender: Sender<oak::grpc::Invocation>,
}

impl oak::WithInit for Router {
    type Init = LogInit;

    fn create(init: Self::Init) -> Self {
        let log_sender = init.log_sender.unwrap();
        oak::logger::init(log_sender.clone(), log::Level::Debug).unwrap();
        let public_key_label = confidentiality_label(web_assembly_module_signature_tag(
            &base64::decode(PUBLIC_KEY_BASE64.as_bytes())
                .expect("Couldn't decode Base64 public key"),
        ));
        let handler_command_sender = oak::io::entrypoint_node_create::<Handler, _, _>(
            "handler",
            &public_key_label,
            "handler",
            LogInit {
                log_sender: Some(log_sender),
            },
        )
        .expect("Couldn't create handler node");

        Self {
            handler_command_sender,
        }
    }
}

impl oak::CommandHandler for Router {
    type Command = oak::grpc::Invocation;

    fn handle_command(&mut self, command: Self::Command) -> anyhow::Result<()> {
        forward_invocation(command, &self.handler_command_sender)
    }
}
