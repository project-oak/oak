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
use log::{info, warn};
use oak::{
    grpc,
    io::{ReceiverExt, Sender, SenderExt},
    Label,
};
use oak_abi::proto::oak::{application::ConfigMap, label::tag};
use oak_services::proto::{
    google::rpc,
    oak::log::{LogInit, LogMessage},
};
use proto::{Chat, ChatDispatcher, Message, SendMessageRequest, SubscribeRequest};
use std::collections::HashMap;

mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.chat.rs"));
}

/// Main entrypoint of the chat application.
///
/// This node is in charge of creating the other top-level nodes, but does not process any request.
#[derive(Default)]
struct Main;

oak::entrypoint_command_handler!(main => Main);

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: ConfigMap) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;
        let router_sender = oak::io::entrypoint_node_create::<Router, _, _>(
            "router",
            &Label::public_untrusted(),
            "app",
            LogInit {
                log_sender: Some(log_sender),
            },
        )
        .expect("could not create router node");
        oak::grpc::server::init_with_sender("[::]:8080", router_sender)
            .expect("could not create gRPC server pseudo-Node");
        Ok(())
    }
}

/// A node that routes each incoming gRPC invocation to a per-room worker node (either pre-existing,
/// or newly created) that can handle requests with the label of the incoming request.
///
/// This node never looks at the contents of the invocation messages, only at the labels of its
/// channels, and therefore keeps a public confidentiality label, which also allows it to create
/// further nodes and channels, with more specific labels.
struct Router {
    /// Maps each label to a channel to a dedicated worker node for that label, corresponding to
    /// the `room` entrypoint of this module.
    rooms: HashMap<Label, Sender<oak::grpc::Invocation>>,
    log_sender: Option<Sender<LogMessage>>,
}

impl oak::WithInit for Router {
    type Init = LogInit;

    fn create(init: Self::Init) -> Self {
        let log_sender = init.log_sender.unwrap();
        oak::logger::init(log_sender.clone(), log::Level::Debug).unwrap();
        Self {
            rooms: HashMap::new(),
            log_sender: Some(log_sender),
        }
    }
}

oak::entrypoint_command_handler_init!(router => Router);

/// Returns whether the provided label is valid in the context of this chat application.
///
/// In principle a client may send requests with arbitrary labels, but only labels with exactly one
/// confidentiality component, itself corresponding to a public key, are actually correctly handled
/// by this application. Any other label would cause the application to get stuck and not be able to
/// declassify data in the future, therefore in this case we fail early with an appropriate error
/// code to the client.
fn is_valid_label(label: &Label) -> bool {
    (label.confidentiality_tags.len() == 1)
        && matches!(
            &label.confidentiality_tags[0].tag,
            Some(tag::Tag::PublicKeyIdentityTag(_))
        )
}

impl oak::CommandHandler for Router {
    type Command = oak::grpc::Invocation;

    fn handle_command(&mut self, command: oak::grpc::Invocation) -> anyhow::Result<()> {
        // The router node has a public confidentiality label, and therefore cannot read the
        // contents of the request of the invocation (unless it happens to be public as well), but
        // it can always inspect its label.
        let result = match (&command.receiver, &command.sender) {
            (Some(receiver), Some(sender)) => {
                let label = receiver.label()?;
                let grpc_response_writer = oak::grpc::ChannelResponseWriter::new(sender.clone());
                if !is_valid_label(&label) {
                    grpc_response_writer
                        .close(Err(oak::grpc::build_status(
                            rpc::Code::InvalidArgument,
                            "invalid request label",
                        )))
                        .context("could not send error response back")?;
                    anyhow::bail!("invalid request label: {:?}", label);
                }
                // Check if there is a channel to a room with the desired label already, or create
                // it if not.
                let log_sender = self.log_sender.clone();
                let channel = self.rooms.entry(label.clone()).or_insert_with(|| {
                    oak::io::entrypoint_node_create::<Room, _, _>(
                        "room",
                        &label,
                        "app",
                        LogInit { log_sender },
                    )
                    .expect("could not create room node")
                });
                // Send the invocation to the dedicated worker node.
                channel.send(&command)?;
                Ok(())
            }
            _ => {
                anyhow::bail!("received malformed gRPC invocation");
            }
        };
        command.close()?;
        result
    }
}

oak::entrypoint_command_handler_init!(room => Room);
oak::impl_dispatcher!(impl Room : ChatDispatcher);

impl oak::WithInit for Room {
    type Init = LogInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self::default()
    }
}

/// A worker node implementation for an individual label, corresponding to a chat room between the
/// set of user that share the key to that chat room.
///
/// Multiple instances of this node may be created at runtime, according to the variety of labels of
/// incoming requests.
#[derive(Default)]
struct Room {
    messages: Vec<Message>,
    clients: Vec<oak::grpc::ChannelResponseWriter>,
}

impl Chat for Room {
    fn subscribe(&mut self, _req: SubscribeRequest, writer: grpc::ChannelResponseWriter) {
        info!("subscribing to room");
        self.clients.push(writer);
    }

    fn send_message(&mut self, req: SendMessageRequest) -> grpc::Result<()> {
        info!("sending message to room");
        match req.message {
            Some(message) => {
                self.messages.push(message.clone());
                // Only retain clients we can write to successfully.
                self.clients.retain(|writer| {
                            if let Err(err) = writer.write(&message, oak::grpc::WriteMode::KeepOpen) {
                                warn!("could not write to client, dropping for future SendMessage invocations: {}", err);
                                // Do not retain writer.
                                false
                            } else {
                                // Retain writer.
                                true
                            }
                        });
                Ok(())
            }
            None => Err(grpc::build_status(
                grpc::Code::InvalidArgument,
                "missing message",
            )),
        }
    }
}
