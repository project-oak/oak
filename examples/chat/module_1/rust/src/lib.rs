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

use chat_common::proto::chat::Message;
use chat_common::Msg;
use log::info;
use protobuf::ProtobufEnum;

#[no_mangle]
pub extern "C" fn backend_oak_main(handle: u64) -> i32 {
    match std::panic::catch_unwind(|| {
        let room = Room::default();
        room.event_loop(handle)
    }) {
        Ok(rc) => rc,
        Err(_) => oak::OakStatus::ERR_INTERNAL.value(),
    }
}

#[derive(Default)]
struct Room {
    messages: Vec<Message>,
    clients: Vec<oak::grpc::ChannelResponseWriter>,
}

impl Room {
    fn event_loop(mut self, in_handle: u64) -> i32 {
        // Wait for something on our single input channel.
        let in_channel = oak::ReadHandle { handle: in_handle };
        loop {
            let ready_status = match oak::wait_on_channels(&[in_channel]) {
                Ok(ready_status) => ready_status,
                Err(err) => {
                    // The other side of the channel was closed.
                    info!("room terminating with {}", err.value());
                    self.close_all();
                    return err.value();
                }
            };
            if ready_status[0] != oak::ChannelReadStatus::READ_READY {
                continue;
            };

            let msg: Msg = chat_common::receive(in_channel).expect("could not receive message");
            match msg {
                Msg::Join(h) => {
                    self.clients.push(oak::grpc::ChannelResponseWriter::new(h));
                }
                Msg::SendMessage(message_bytes) => {
                    let message: Message = protobuf::parse_from_bytes(&message_bytes)
                        .expect("could not parse message from bytes");
                    self.messages.push(message.clone());
                    info!("fan out message to {} clients", self.clients.len());
                    for writer in &mut self.clients {
                        writer.write(&message, oak::grpc::WriteMode::KeepOpen);
                    }
                }
            }
        }
    }

    fn close_all(&mut self) {
        for writer in &mut self.clients {
            writer.close(Ok(()));
        }
    }
}
