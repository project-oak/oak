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

use crate::command::Command;
use crate::proto::chat::Message;
use log::info;
use oak::Node;

oak::entrypoint!(backend_oak_main => {
    oak_log::init_default();
    Room::default()
});

#[derive(Default)]
struct Room {
    messages: Vec<Message>,
    clients: Vec<oak::grpc::ChannelResponseWriter>,
}

impl Node<Command> for Room {
    fn handle_command(&mut self, command: Command) -> Result<(), oak::OakError> {
        match command {
            Command::Join(h) => {
                let sender = oak::io::Sender::new(h);
                self.clients
                    .push(oak::grpc::ChannelResponseWriter::new(sender));
                Ok(())
            }
            Command::SendMessage(message_bytes) => {
                let message: Message = protobuf::parse_from_bytes(&message_bytes)
                    .expect("could not parse message from bytes");
                self.messages.push(message.clone());
                info!("fan out message to {} clients", self.clients.len());
                for writer in &mut self.clients {
                    // TODO: Improve error handling.
                    writer
                        .write(&message, oak::grpc::WriteMode::KeepOpen)
                        .expect("could not write to channel");
                }
                Ok(())
            }
        }
    }
}
