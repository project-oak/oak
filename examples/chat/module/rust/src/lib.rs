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

mod proto;

use log::info;
use oak::grpc;
use oak::grpc::OakNode;
use oak_derive::OakExports;
use proto::chat::{CreateRoomRequest, DestroyRoomRequest};
use proto::chat::{JoinRoomRequest, ReceivedMessage, SentMessage};
use proto::chat_grpc::{dispatch, ChatNode};
use protobuf::well_known_types::Empty;
use protobuf::ProtobufEnum;
use std::collections::HashMap;

type RoomId = Vec<u8>;
type AdminId = Vec<u8>;

#[derive(OakExports)]
struct Node {
    room_to_admin: HashMap<RoomId, AdminId>,
    admin_to_room: HashMap<AdminId, RoomId>,
    rooms: HashMap<AdminId, Room>,
}

impl OakNode for Node {
    fn new() -> Self {
        oak_log::init_default();
        Node {
            room_to_admin: HashMap::new(),
            admin_to_room: HashMap::new(),
            rooms: HashMap::new(),
        }
    }
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

fn unknown_id_err<T>(which: &str) -> grpc::Result<T> {
    Err(grpc::build_status(
        grpc::Code::INVALID_ARGUMENT,
        &format!("{} ID unrecognized", which),
    ))
}

fn duplicate_id_err<T>(which: &str) -> grpc::Result<T> {
    Err(grpc::build_status(
        grpc::Code::ALREADY_EXISTS,
        &format!("{} ID already exists", which),
    ))
}

impl ChatNode for Node {
    fn create_room(&mut self, req: CreateRoomRequest) -> grpc::Result<Empty> {
        info!("Create new room {}", req.name);
        if self.rooms.contains_key(&req.admin_id) {
            return duplicate_id_err("Admin");
        }
        if self.room_to_admin.contains_key(&req.room_id) {
            return duplicate_id_err("Room");
        }
        self.rooms.insert(
            req.admin_id.clone(),
            Room {
                name: req.name,
                writers: Vec::new(),
            },
        );
        self.room_to_admin
            .insert(req.room_id.clone(), req.admin_id.clone());
        self.admin_to_room
            .insert(req.admin_id.clone(), req.room_id.clone());
        Ok(Empty::new())
    }

    fn destroy_room(&mut self, req: DestroyRoomRequest) -> grpc::Result<Empty> {
        if !self.rooms.contains_key(&req.admin_id) {
            return unknown_id_err("Admin");
        }
        let room = self.rooms.get_mut(&req.admin_id).unwrap();
        info!("Destroying room {}", room.name);
        room.clear();
        let user_id = self.admin_to_room.get(&req.admin_id).unwrap().clone();
        self.admin_to_room.remove(&req.admin_id);
        self.room_to_admin.remove(&user_id);
        self.rooms.remove(&req.admin_id);
        Ok(Empty::new())
    }

    fn join_room(&mut self, req: JoinRoomRequest, mut writer: grpc::ChannelResponseWriter) {
        if !self.room_to_admin.contains_key(&req.room_id) {
            writer.close(unknown_id_err("Room"));
            return;
        }

        let admin_id = self.room_to_admin.get(&req.room_id).unwrap();
        let room = self.rooms.get_mut(admin_id).unwrap();
        room.writers.push(writer);

        // Send a joining announcement.
        info!("{} has joined room {}", req.user_handle, room.name);
        room.broadcast(
            "<server>",
            &format!("{} has joined room {}", req.user_handle, room.name).to_string(),
        );
    }

    fn send_message(&mut self, req: SentMessage) -> grpc::Result<Empty> {
        if !self.room_to_admin.contains_key(&req.room_id) {
            return unknown_id_err("Room");
        }
        let admin_id = self.room_to_admin.get(&req.room_id).unwrap();
        let room = self.rooms.get_mut(admin_id).unwrap();
        room.broadcast(&req.user_handle, &req.text);
        Ok(Empty::new())
    }
}

struct Room {
    name: String,
    writers: Vec<grpc::ChannelResponseWriter>,
}

impl Room {
    fn broadcast(&mut self, from: &str, text: &str) {
        info!("broadcast {}: {}", from, text);
        let mut msg = ReceivedMessage::new();
        msg.room_name = self.name.clone();
        msg.user_handle = from.to_string();
        msg.text = text.to_string();
        for writer in &mut self.writers {
            writer.write(msg.clone(), grpc::WriteMode::KeepOpen);
        }
    }
    // Close all writers associated with the room.
    fn clear(&mut self) {
        info!("clear room {}", self.name);
        for writer in &mut self.writers {
            writer.close(Ok(()));
        }
    }
}
