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
use proto::{
    Chat, ChatDispatcher, CreateRoomRequest, DestroyRoomRequest, Message, SendMessageRequest,
    SubscribeRequest,
};
use std::collections::HashMap;

mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.chat.rs"));
}

type AdminToken = Vec<u8>;

#[derive(Default)]
struct Router {
    rooms: HashMap<Label, Sender<oak::grpc::Invocation>>,
}

impl oak::CommandHandler<oak::grpc::Invocation> for Router {
    fn handle_command(&mut self, command: oak::grpc::Invocation) -> Result<(), oak::OakError> {
        match &command.receiver {
            Some(receiver) => {
                let label = receiver.label()?;
                let channel = self.rooms.entry(label.clone()).or_insert_with(|| {
                    let (wh, rh) = oak::io::channel_create_with_label(&label)
                        .expect("could not create channel");
                    oak::node_create(&oak::node_config::wasm("app", "room"), rh.handle)
                        .expect("could not create node");
                    rh.close().expect("could not close channel");
                    wh
                });
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

oak::entrypoint!(grpc_oak_main => |_in_channel| {
    oak::logger::init_default();
    let router = Router::default();
    let grpc_channel =
        oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
    oak::run_command_loop(router, grpc_channel);
});

oak::entrypoint!(room => |in_channel| {
    oak::logger::init_default();
    let dispatcher = ChatDispatcher::new(Room::default());
    oak::run_command_loop(dispatcher, in_channel);
});

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
