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

pub mod proto;

use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub enum Msg {
    Join(oak::WriteHandle),
    // TODO: Embed native Message struct here when we support proto serialization via Serde.
    // See https://github.com/stepancheg/rust-protobuf#serde_derive-support
    SendMessage(Vec<u8>),
}

// TODO(#389): Automatically generate this code.
// Currently we use [bincode](https://github.com/servo/bincode) to serialize data together with a
// tag that allows to reconstruct the enum variant on the other side. We then send the tag+data as
// bytes, and separately we send the handles, which we have to manually re-assemble on the other
// side.
impl Msg {
    pub fn send(&self, write_handle: oak::WriteHandle) -> Result<()> {
        let bytes = bincode::serialize(self).context("could not serialize message to bincode")?;
        // Serialize handles.
        let handles = match self {
            Msg::Join(h) => vec![h.handle],
            Msg::SendMessage(_) => vec![],
        };
        let status = oak::channel_write(write_handle, &bytes, &handles);
        if status == oak::OakStatus::OK {
            Ok(())
        } else {
            Err(anyhow!("could not write to channel"))
        }
    }

    pub fn receive(read_handle: oak::ReadHandle) -> Result<Self> {
        let mut bytes = Vec::<u8>::with_capacity(512);
        let mut handles = Vec::with_capacity(2);
        let status = oak::channel_read(read_handle, &mut bytes, &mut handles);
        if status == oak::OakStatus::OK {
            let msg: Msg = bincode::deserialize(&bytes)
                .context("could not deserialize message from bincode")?;
            // Restore handles in the received message.
            let msg = match msg {
                Msg::Join(_) => Msg::Join(oak::WriteHandle { handle: handles[0] }),
                Msg::SendMessage(message_bytes) => Msg::SendMessage(message_bytes),
            };
            Ok(msg)
        } else {
            Err(anyhow!("could not read from channel"))
        }
    }
}
