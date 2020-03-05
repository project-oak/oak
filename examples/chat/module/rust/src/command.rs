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

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub enum Command {
    Join(oak::WriteHandle),
    // TODO: Embed native Message struct here when we support proto serialization via Serde.
    // See https://github.com/stepancheg/rust-protobuf#serde_derive-support
    SendMessage(Vec<u8>),
}

// TODO(#389): Automatically generate this code.
//
// Currently we use [bincode](https://github.com/servo/bincode) to serialize data together with a
// tag that allows to reconstruct the enum variant on the other side. We then send the tag+data as
// bytes, and separately we send the handles, which we have to manually re-assemble on the other
// side.
//
// FIDL implements something similar to this in
// https://fuchsia.googlesource.com/fuchsia/+/refs/heads/master/garnet/public/lib/fidl/rust/fidl/src/encoding.rs.
impl oak::io::Encodable for Command {
    fn encode(&self) -> Result<oak::io::Message, oak::OakError> {
        // TODO: Propagate more details about the source error.
        let bytes = bincode::serialize(self).map_err(|_| oak::OakStatus::ErrInvalidArgs)?;
        // Serialize handles separately.
        let handles = match self {
            Command::Join(h) => vec![h.handle],
            Command::SendMessage(_) => vec![],
        };
        Ok(oak::io::Message { bytes, handles })
    }
}

// TODO(#389): Automatically generate this code.
impl oak::io::Decodable for Command {
    fn decode(message: &oak::io::Message) -> Result<Self, oak::OakError> {
        // TODO: Propagate more details about the source error.
        let command: Command =
            bincode::deserialize(&message.bytes).map_err(|_| oak::OakStatus::ErrInvalidArgs)?;
        // Restore handles in the received message.
        let command = match command {
            Command::Join(_) => Command::Join(oak::WriteHandle {
                handle: message.handles[0],
            }),
            Command::SendMessage(message_bytes) => Command::SendMessage(message_bytes),
        };
        Ok(command)
    }
}
