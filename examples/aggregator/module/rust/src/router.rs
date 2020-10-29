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
use anyhow::Context;
use oak::io::{ReceiverExt, Sender, SenderExt};
use oak_abi::label::{confidentiality_label, web_assembly_module_tag, Label};
use oak_services::proto::google::rpc;

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
    /// Confidentiality label corresponding to Aggregator WebAssembly module SHA-256 hash.
    aggregator_hash_label: Label,
}

impl oak::CommandHandler for Router {
    type Command = oak::grpc::Invocation;

    fn handle_command(&mut self, command: oak::grpc::Invocation) -> anyhow::Result<()> {
        // The router node has a public confidentiality label, and therefore cannot read the
        // contents of the request of the invocation (unless it happens to be public as well), but
        // it can always inspect its label.
        match (&command.receiver, &command.sender) {
            (Some(receiver), Some(sender)) => {
                let label = receiver.label()?;
                let grpc_response_writer = oak::grpc::ChannelResponseWriter::new(sender.clone());
                // Check if request label is valid in the context of Aggregator application.
                if !label.flows_to(&self.aggregator_hash_label) {
                    grpc_response_writer
                        .close(Err(oak::grpc::build_status(
                            rpc::Code::InvalidArgument,
                            "Invalid request label",
                        )))
                        .context("Couldn't send error response back")?;
                    anyhow::bail!("Invalid request label: {:?}", label);
                }

                // Route gRPC invocations to Handler Node.
                self.handler_invocation_sender
                    .send(&command)
                    .context("Couldn't send invocation to worker node")
            }
            _ => {
                anyhow::bail!("Received malformed gRPC invocation");
            }
        }
    }
}

impl oak::WithInit for Router {
    type Init = RouterInit;

    fn create(init: Self::Init) -> Self {
        let handler_invocation_sender = init
            .handler_invocation_sender
            .expect("Couldn't receive gRPC invocation sender")
            .sender
            .expect("Empty gRPC invocation sender");
        let aggregator_hash_label = confidentiality_label(web_assembly_module_tag(
            &hex::decode(init.aggregator_module_hash).expect("Couldn't decode SHA-256 hex value"),
        ));
        Self {
            handler_invocation_sender,
            aggregator_hash_label,
        }
    }
}

oak::entrypoint_command_handler_init!(router => Router);
