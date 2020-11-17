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

//! Private Set Intersection example for Project Oak.
//!
//! Clients invoke the module by providing their own private set, and the module keeps track of the
//! intersection of all the provided sets from all the clients that have interacted with it.
//! The number of contributed private sets is limited and defined by `SET_THRESHOLD`.
//!
//! The (common) intersection can then be retrieved by each client by a separate invocation.
//! After the first client retrieves the intersection it becomes locked, and new contributions are
//! discarded.
//!
//! Each client request should be provided with a set ID. This is necessary for allowing multiple
//! sets of clients to compute their own intersections.
//!
//! It's important to note that in the current implementation of the application labels, specifying
//! a different set ID does not provide guarantees that data from different clients is kept
//! separate.

pub mod proto {
    include!(concat!(
        env!("OUT_DIR"),
        "/oak.examples.private_set_intersection.rs"
    ));
}

pub mod handler;

use crate::handler::Handler;
use anyhow::Context;
use oak::{
    io::{ReceiverExt, Sender, SenderExt},
    Label,
};
use oak_abi::{
    label::{confidentiality_label, web_assembly_module_signature_tag},
    proto::oak::application::ConfigMap,
};
use oak_services::proto::google::rpc;

// Base64 encoded Ed25519 public key corresponding to Wasm module signature.
// Originated from `examples/keys/ed25519/test.pub`.
const PUBLIC_KEY_BASE64: &str = "f41SClNtR4i46v2Tuh1fQLbt/ZqRr1lENajCW92jyP4=";

oak::entrypoint_command_handler!(oak_main => Main);

#[derive(Default)]
struct Main;

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: ConfigMap) -> anyhow::Result<()> {
        let router_command_sender =
            oak::io::entrypoint_node_create::<Router>("router", &Label::public_untrusted(), "app")
                .context("Couldn't create router node")?;

        oak::grpc::server::init_with_sender("[::]:8080", router_command_sender)
            .context("Couldn't create gRPC server pseudo-Node")?;
        Ok(())
    }
}

oak::entrypoint_command_handler!(router => Router);

struct Router {
    /// Invocation sender channel half for Handler Node.
    handler_command_sender: Sender<oak::grpc::Invocation>,
    /// Confidentiality label corresponding to WebAssembly signature public key.
    public_key_label: Label,
}

impl Default for Router {
    fn default() -> Self {
        let public_key_label = confidentiality_label(web_assembly_module_signature_tag(
            &base64::decode(PUBLIC_KEY_BASE64.as_bytes())
                .expect("Couldn't decode Base64 public key"),
        ));
        let handler_command_sender =
            oak::io::entrypoint_node_create::<Handler>("handler", &public_key_label, "app")
                .expect("Couldn't create handler node");

        Self {
            handler_command_sender,
            public_key_label,
        }
    }
}

impl oak::CommandHandler for Router {
    type Command = oak::grpc::Invocation;

    fn handle_command(&mut self, command: oak::grpc::Invocation) -> anyhow::Result<()> {
        match (&command.receiver, &command.sender) {
            (Some(receiver), Some(sender)) => {
                let label = receiver.label()?;
                // Check if request label is valid in the context of Private Set Intersection
                // application.
                if !label.flows_to(&self.public_key_label) {
                    let grpc_response_writer =
                        oak::grpc::ChannelResponseWriter::new(sender.clone());
                    grpc_response_writer
                        .close(Err(oak::grpc::build_status(
                            rpc::Code::InvalidArgument,
                            "Invalid request label",
                        )))
                        .context("Couldn't send error response back")?;
                    anyhow::bail!("Invalid request label: {:?}", label);
                }

                // Route gRPC invocations to Handler Node.
                self.handler_command_sender
                    .send(&command)
                    .context("Couldn't send invocation to worker node")
            }
            _ => {
                anyhow::bail!("Received malformed gRPC invocation");
            }
        }
    }
}
