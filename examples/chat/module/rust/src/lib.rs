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

use chat_common::proto::chat::{CreateRoomRequest, DestroyRoomRequest};
use chat_common::proto::chat::{JoinRoomRequest, ReceivedMessage, SentMessage};
use chat_common::proto::chat_grpc::{dispatch, ChatNode};
use log::info;
use oak::grpc;
use oak::grpc::OakNode;
use oak_derive::OakExports;
use protobuf::well_known_types::Empty;
use protobuf::{Message, ProtobufEnum};
use std::collections::HashMap;

type RoomId = Vec<u8>;
type AdminId = Vec<u8>;

#[derive(OakExports)]
struct Node {
    // TODO: use bimap crate for these fields?
    room_to_admin: HashMap<RoomId, AdminId>,
    admin_to_room: HashMap<AdminId, RoomId>,
    rooms: HashMap<AdminId, Room>,
}

struct Room {
    name: String,
    channel: oak::WriteHandle,
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

        // Create a new Node for this room.
        let (wh, rh) = oak::channel_create().unwrap();
        oak::node_create("room-config", rh);
        oak::channel_close(rh.handle);

        self.rooms.insert(
            req.admin_id.clone(),
            Room {
                name: req.name,
                channel: wh,
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

        // Close the only input channel that reaches the per-room Node, which
        // will trigger it to terminate.
        oak::channel_close(room.channel.handle);
        let user_id = self.admin_to_room.get(&req.admin_id).unwrap().clone();
        self.admin_to_room.remove(&req.admin_id);
        self.room_to_admin.remove(&user_id);
        self.rooms.remove(&req.admin_id);
        Ok(Empty::new())
    }

    fn join_room(&mut self, req: JoinRoomRequest, mut writer: grpc::ChannelResponseWriter) {
        let admin_id = match self.room_to_admin.get(&req.room_id) {
            None => {
                writer.close(unknown_id_err("Room"));
                return;
            }
            Some(id) => id,
        };
        let room = self.rooms.get_mut(admin_id).unwrap();

        // Send a joining announcement, including a handle to be included in
        // future per-room broadcasts.
        let rsp_handle = writer.handle().handle;
        info!("{} has joined room {}", req.user_handle, room.name);
        room.broadcast(
            "<server>",
            &format!("{} has joined room {}", req.user_handle, room.name).to_string(),
            Some(rsp_handle),
        );
        // Now that the backend has a reference to the response channel, we can close
        // our reference to the underlying channel.
        oak::channel_close(rsp_handle);
    }

    fn send_message(&mut self, req: SentMessage) -> grpc::Result<Empty> {
        let admin_id = match self.room_to_admin.get(&req.room_id) {
            None => return unknown_id_err("Room"),
            Some(id) => id,
        };
        let room = self.rooms.get_mut(admin_id).unwrap();
        room.broadcast(&req.user_handle, &req.text, None);
        Ok(Empty::new())
    }
}

impl Room {
    fn broadcast(&self, from: &str, text: &str, handle: Option<oak::Handle>) {
        info!("broadcast({:?}) {}: {}", handle, from, text);
        let mut msg = ReceivedMessage::new();
        msg.room_name = self.name.clone();
        msg.user_handle = from.to_string();
        msg.text = text.to_string();

        let mut data = Vec::new();
        msg.write_to_writer(&mut data).unwrap();

        let mut handles = Vec::new();
        if let Some(h) = handle {
            handles.push(h);
        }
        oak::channel_write(self.channel, &data, &handles);
    }
}
