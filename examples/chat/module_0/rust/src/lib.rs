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

use chat_common::command::Command;
use chat_common::proto::chat::{
    CreateRoomRequest, DestroyRoomRequest, SendMessageRequest, SubscribeRequest,
};
use chat_common::proto::chat_grpc::{dispatch, ChatNode};
use log::info;
use oak::grpc;
use oak::grpc::OakNode;
use oak_derive::OakExports;
use protobuf::well_known_types::Empty;
use protobuf::Message;
use std::collections::hash_map::Entry;
use std::collections::HashMap;

type RoomId = Vec<u8>;
type AdminToken = Vec<u8>;

#[derive(OakExports, Default)]
struct Node {
    rooms: HashMap<RoomId, Room>,
}

struct Room {
    sender: oak::io::Sender<Command>,
    admin_token: AdminToken,
}

impl Room {
    fn new(admin_token: AdminToken) -> Self {
        let (wh, rh) = oak::channel_create().unwrap();
        oak::node_create("room-config", "backend_oak_main", rh).expect("could not create node");
        oak::channel_close(rh.handle).expect("could not close channel");
        Room {
            sender: oak::io::Sender::new(wh),
            admin_token,
        }
    }
}

impl OakNode for Node {
    fn new() -> Self {
        oak_log::init_default();
        Node::default()
    }
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

fn room_id_not_found_err<T>() -> grpc::Result<T> {
    Err(grpc::build_status(grpc::Code::NOT_FOUND, "room not found"))
}

fn room_id_duplicate_err<T>() -> grpc::Result<T> {
    Err(grpc::build_status(
        grpc::Code::ALREADY_EXISTS,
        "room already exists",
    ))
}

impl ChatNode for Node {
    fn create_room(&mut self, req: CreateRoomRequest) -> grpc::Result<Empty> {
        info!("creating room");
        if self.rooms.contains_key(&req.room_id) {
            return room_id_duplicate_err();
        }

        // Create a new Node for this room, and keep the write handle and admin token in the `rooms`
        // map.
        self.rooms.insert(req.room_id, Room::new(req.admin_token));

        Ok(Empty::new())
    }

    fn destroy_room(&mut self, req: DestroyRoomRequest) -> grpc::Result<Empty> {
        info!("destroying room");
        match self.rooms.entry(req.room_id) {
            Entry::Occupied(e) => {
                if e.get().admin_token == req.admin_token {
                    // Close the only input channel that reaches the per-room Node, which
                    // will trigger it to terminate.
                    e.get().sender.close().expect("could not close channel");
                    e.remove();
                    Ok(Empty::new())
                } else {
                    Err(grpc::build_status(
                        grpc::Code::PERMISSION_DENIED,
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

    fn send_message(&mut self, req: SendMessageRequest) -> grpc::Result<Empty> {
        info!("sending message to room");
        match self.rooms.get(&req.room_id) {
            None => room_id_not_found_err(),
            Some(room) => {
                info!("new message to room {:?}", req.room_id);
                let message_bytes = req
                    .get_message()
                    .write_to_bytes()
                    .expect("could not convert message to bytes");
                let command = Command::SendMessage(message_bytes);
                room.sender
                    .send(&command)
                    .expect("could not send command to room Node");
                Ok(Empty::new())
            }
        }
    }
}
