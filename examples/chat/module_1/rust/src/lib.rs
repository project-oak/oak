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
use chat_common::proto::chat::Message;
use log::{error, info, warn};

#[no_mangle]
pub extern "C" fn backend_oak_main(handle: u64) {
    let _ = std::panic::catch_unwind(|| {
        oak_log::init_default();
        oak::set_panic_hook();
        let room = Room::default();
        if let Err(s) = room.event_loop(handle) {
            warn!("backend Node terminating with {:?}", s);
        }
    });
}

#[derive(Default)]
struct Room {
    messages: Vec<Message>,
    clients: Vec<oak::grpc::ChannelResponseWriter>,
}

impl Room {
    fn event_loop(mut self, in_handle: u64) -> Result<(), oak::OakError> {
        // Wait for something on our single input channel.
        let in_channel = oak::ReadHandle {
            handle: oak::Handle::from_raw(in_handle),
        };
        let receiver = oak::io::Receiver::new(in_channel);
        info!("starting event loop");
        loop {
            info!("reading incoming command");
            let command: Command = receiver.receive()?;
            if let Err(e) = self.handle_command(command) {
                self.close_all();
                return Err(e);
            }
        }
    }

    fn handle_command(&mut self, command: Command) -> Result<(), oak::OakError> {
        match command {
            Command::Join(h) => {
                self.clients.push(oak::grpc::ChannelResponseWriter::new(h));
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

    fn close_all(&mut self) {
        for writer in &mut self.clients {
            writer
                .close(Ok(()))
                .unwrap_or_else(|err| error!("could not close channel: {:?}", err))
        }
    }
}
