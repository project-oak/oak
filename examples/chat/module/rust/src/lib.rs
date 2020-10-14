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

use log::{error, info, warn};
use oak::{
    grpc,
    io::{ReceiverExt, Sender, SenderExt},
    Label,
};
use oak_abi::proto::oak::application::ConfigMap;
use proto::{
    Chat, ChatDispatcher, CreateRoomRequest, DestroyRoomRequest, Message, SendMessageRequest,
    SubscribeRequest,
};
use std::collections::HashMap;

mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.chat.rs"));
}

type AdminToken = Vec<u8>;

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

impl oak::CommandHandler<oak::grpc::Invocation> for Router {
    fn handle_command(&mut self, command: oak::grpc::Invocation) -> Result<(), oak::OakError> {
        // The router node has a public confidentiality label, and therefore cannot read the
        // contents of the request of the invocation (unless it happens to be public as well), but
        // it can always inspect its label.
        match &command.receiver {
            Some(receiver) => {
                let label = receiver.label()?;
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
            None => {
                error!("received gRPC invocation without request channel");
                Err(oak::OakStatus::ErrInvalidArgs.into())
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
oak::entrypoint!(room => |in_channel| {
    oak::logger::init_default();
    let dispatcher = ChatDispatcher::new(Room::default());
    oak::run_command_loop(dispatcher, in_channel);
});

/// A worker node implementation for an individual label.
///
/// It is initially uninitialized, and it expects to receive a `create_room` message as its first
/// request; this initializes the inner field, and moves the node to the initialized state, from
/// which it receives messages from clients and sends out replies to subscribed clients.
#[derive(Default)]
struct Room {
    inner: Option<RoomInner>,
}

struct RoomInner {
    admin_token: AdminToken,
    messages: Vec<Message>,
    clients: Vec<oak::grpc::ChannelResponseWriter>,
}

impl RoomInner {
    fn new(admin_token: AdminToken) -> Self {
        RoomInner {
            admin_token,
            messages: Vec::new(),
            clients: Vec::new(),
        }
    }
}

fn room_id_not_found_err<T>() -> grpc::Result<T> {
    Err(grpc::build_status(grpc::Code::NotFound, "room not found"))
}

fn room_id_duplicate_err<T>() -> grpc::Result<T> {
    Err(grpc::build_status(
        grpc::Code::AlreadyExists,
        "room already exists",
    ))
}

impl Chat for Room {
    fn create_room(&mut self, req: CreateRoomRequest) -> grpc::Result<()> {
        info!("creating room");
        match self.inner {
            None => {
                self.inner = Some(RoomInner::new(req.admin_token));
                Ok(())
            }
            Some(_) => room_id_duplicate_err(),
        }
    }

    fn destroy_room(&mut self, req: DestroyRoomRequest) -> grpc::Result<()> {
        info!("destroying room");
        match &self.inner {
            Some(room) => {
                if room.admin_token == req.admin_token {
                    // TODO: Trigger this node termination, so that the router node may notice and
                    // clean up any associated state.
                    Ok(())
                } else {
                    Err(grpc::build_status(
                        grpc::Code::PermissionDenied,
                        "invalid admin token",
                    ))
                }
            }
            None => room_id_not_found_err(),
        }
    }

    fn subscribe(&mut self, _req: SubscribeRequest, writer: grpc::ChannelResponseWriter) {
        info!("subscribing to room");
        match &mut self.inner {
            Some(room) => {
                info!("new subscription to room");
                room.clients.push(writer);
            }
            None => {
                if let Err(err) = writer.close(room_id_not_found_err()) {
                    warn!("could not close channel: {}", err);
                }
            }
        };
    }

    fn send_message(&mut self, req: SendMessageRequest) -> grpc::Result<()> {
        info!("sending message to room");
        match &mut self.inner {
            Some(room) => {
                info!("new message to room");
                match req.message {
                    Some(message) => {
                        room.messages.push(message.clone());
                        // Only retain clients we can write to successfully.
                        room.clients.retain(|writer| {
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
            None => room_id_not_found_err(),
        }
    }
}
