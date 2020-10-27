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
use oak_abi::proto::oak::application::ConfigMap;
use oak_services::proto::google::rpc;
use proto::{Chat, ChatDispatcher, Message, SendMessageRequest, SubscribeRequest};
use std::collections::HashMap;

mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.chat.rs"));
}

/// A node that routes each incoming gRPC invocation to a per-room worker node (either pre-existing,
/// or newly created) that can handle requests with the label of the incoming request.
///
/// This node never looks at the contents of the invocation messages, only at the labels of its
/// channels, and therefore keeps a public confidentiality label, which also allows it to create
/// further nodes and channels, with more specific labels.
#[derive(Default)]
struct Router {
    /// Maps each label to a channel to a dedicated worker node for that label, corresponding to
    /// the `room` entry point of this module.
    rooms: HashMap<Label, Sender<oak::grpc::Invocation>>,
}

/// Returns whether the provided label is valid in the context of this chat application.
///
/// In principle a client may send requests with arbitrary labels, but only labels with exactly one
/// confidentiality component, itself corresponding to a public key, are actually correctly handled
/// by this application. Any other label would cause the application to get stuck and not be able to
/// declassify data in the future, therefore in this case we fail early with an appropriate error
/// code to the client.
fn is_valid_label(_label: &Label) -> bool {
    true
    // TODO(#1357): Verify that the label corresponds to exactly a single PublicKeyIdentityTag.
    // (label.confidentiality_tags.len() == 1)
    //     && (if let Some(tag) = &label.confidentiality_tags[0].tag {
    //         match tag {
    //             tag::Tag::GrpcTag(_) => true,
    //             _ => false,
    //         }
    //     } else {
    //         false
    //     })
}

impl oak::CommandHandler<oak::grpc::Invocation> for Router {
    fn handle_command(&mut self, command: oak::grpc::Invocation) -> anyhow::Result<()> {
        // The router node has a public confidentiality label, and therefore cannot read the
        // contents of the request of the invocation (unless it happens to be public as well), but
        // it can always inspect its label.
        match (&command.receiver, &command.sender) {
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
                let channel = self.rooms.entry(label.clone()).or_insert_with(|| {
                    let (wh, rh) = oak::io::channel_create_with_label(&label)
                        .expect("could not create channel");
                    oak::node_create_with_label(
                        &oak::node_config::wasm("app", "room"),
                        &label,
                        rh.handle,
                    )
                    .expect("could not create node");
                    rh.close().expect("could not close channel");
                    wh
                });
                // Send the invocation to the dedicated worker node.
                channel.send(&command)?;
                Ok(())
            }
            _ => {
                anyhow::bail!("received malformed gRPC invocation");
            }
        }
    }
}

// Main entrypoint of the chat application.
oak::entrypoint!(grpc_oak_main<ConfigMap> => |_receiver| {
    oak::logger::init_default();
    let router = Router::default();
    let grpc_channel =
        oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
    oak::run_command_loop(router, grpc_channel);
});

// A node that receives gRPC invocations for an individual label.
//
// Multiple instances of nodes with this entrypoint may be created at runtime, according to the
// variety of labels of incoming requests.
oak::entrypoint!(room<oak::grpc::Invocation> => |receiver| {
    oak::logger::init_default();
    let dispatcher = ChatDispatcher::new(Room::default());
    oak::run_command_loop(dispatcher, receiver);
});

/// A worker node implementation for an individual label.
///
/// It is initially uninitialized, and it expects to receive a `create_room` message as its first
/// request; this initializes the inner field, and moves the node to the initialized state, from
/// which it receives messages from clients and sends out replies to subscribed clients.
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
