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

use crate::proto::{
    command::Command::{JoinRoom, SendMessage},
    Command, Message,
};
use log::{info, warn};
use oak::Node;

oak::entrypoint!(backend_oak_main => |in_channel| {
    oak::logger::init_default();
    oak::run_event_loop(Room::default(), oak::io::Receiver::<Command>::new(in_channel));
});

#[derive(Default)]
struct Room {
    messages: Vec<Message>,
    clients: Vec<oak::grpc::ChannelResponseWriter>,
}

impl Node<Command> for Room {
    fn handle_command(&mut self, command: Command) -> Result<(), oak::OakError> {
        match command.command {
            Some(JoinRoom(sender)) => {
                self.clients
                    .push(oak::grpc::ChannelResponseWriter::new(sender));
                Ok(())
            }
            Some(SendMessage(message)) => {
                self.messages.push(message.clone());
                info!("fan out message to {} clients", self.clients.len());
                for writer in &mut self.clients {
                    // TODO(#746): Improve error handling.
                    writer
                        .write(&message, oak::grpc::WriteMode::KeepOpen)
                        .expect("could not write to channel");
                }
                Ok(())
            }
            None => {
                warn!("Received empty command");
                Err(oak::OakError::OakStatus(oak::OakStatus::ErrInvalidArgs))
            }
        }
    }
}
