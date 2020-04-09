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

use command::Command;
use log::info;
use oak::grpc;
use prost::Message;
use proto::{
    Chat, ChatDispatcher, CreateRoomRequest, DestroyRoomRequest, SendMessageRequest,
    SubscribeRequest,
};
use std::collections::hash_map::Entry;
use std::collections::HashMap;

mod backend;
mod command;
mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.chat.rs"));
}

type RoomId = Vec<u8>;
type AdminToken = Vec<u8>;

#[derive(Default)]
struct Node {
    rooms: HashMap<RoomId, Room>,
}

oak::entrypoint!(oak_main => {
    oak::logger::init_default();
    ChatDispatcher::new(Node::default())
});

struct Room {
    sender: oak::io::Sender<Command>,
    admin_token: AdminToken,
}

impl Room {
    fn new(admin_token: AdminToken) -> Self {
        let (wh, rh) = oak::channel_create().unwrap();
        oak::node_create("app", "backend_oak_main", rh).expect("could not create node");
        oak::channel_close(rh.handle).expect("could not close channel");
        Room {
            sender: oak::io::Sender::new(wh),
            admin_token,
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

impl Chat for Node {
    fn create_room(&mut self, req: CreateRoomRequest) -> grpc::Result<()> {
        info!("creating room");
        if self.rooms.contains_key(&req.room_id) {
            return room_id_duplicate_err();
        }

        // Create a new Node for this room, and keep the write handle and admin token in the `rooms`
        // map.
        self.rooms.insert(req.room_id, Room::new(req.admin_token));

        Ok(())
    }

    fn destroy_room(&mut self, req: DestroyRoomRequest) -> grpc::Result<()> {
        info!("destroying room");
        match self.rooms.entry(req.room_id) {
            Entry::Occupied(e) => {
                if e.get().admin_token == req.admin_token {
                    // Close the only input channel that reaches the per-room Node, which
                    // will trigger it to terminate.
                    e.get().sender.close().expect("could not close channel");
                    e.remove();
                    Ok(())
                } else {
                    Err(grpc::build_status(
                        grpc::Code::PermissionDenied,
                        "invalid admin token",
                    ))
                }
            }
            Entry::Vacant(_) => room_id_not_found_err(),
        }
    }

    fn subscribe(&mut self, req: SubscribeRequest, mut writer: grpc::ChannelResponseWriter) {
        info!("subscribing to room");
        match self.rooms.get(&req.room_id) {
            None => {
                writer
                    .close(room_id_not_found_err())
                    .expect("could not close channel");
            }
            Some(room) => {
                info!("new subscription to room {:?}", req.room_id);
                let command = Command::Join(writer.handle());
                room.sender
                    .send(&command)
                    .expect("could not send command to room Node");
            }
        };
    }

    fn send_message(&mut self, req: SendMessageRequest) -> grpc::Result<()> {
        info!("sending message to room");
        match self.rooms.get(&req.room_id) {
            None => room_id_not_found_err(),
            Some(room) => {
                info!("new message to room {:?}", req.room_id);
                let mut message_bytes = Vec::new();
                req.message
                    .unwrap_or_default()
                    .encode(&mut message_bytes)
                    .expect("could not convert message to bytes");
                let command = Command::SendMessage(message_bytes);
                room.sender
                    .send(&command)
                    .expect("could not send command to room Node");
                Ok(())
            }
        }
    }
}
