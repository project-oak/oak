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

pub mod command;
pub mod proto;

use anyhow::{anyhow, Context, Result};

/// A trait for objects that can be encoded as bytes + handles.
///
/// TODO(#457): Move to SDK crate.
pub trait Encodable {
    fn encode(&self) -> Result<(Vec<u8>, Vec<oak::Handle>)>;
}

/// A trait for objects that can be decoded from bytes + handles.
///
/// TODO(#457): Move to SDK crate.
pub trait Decodable: Sized {
    fn decode(bytes: &[u8], handles: &[oak::Handle]) -> Result<Self>;
}

pub fn send<M: Encodable>(write_handle: oak::WriteHandle, msg: M) -> Result<()> {
    let (bytes, handles) = msg.encode().context("could not encode object")?;
    // TODO(#457): Propagate error code to caller.
    oak::channel_write(write_handle, &bytes, &handles)
        .map_err(|status| anyhow!("could not write to channel: {:?}", status))
}

pub fn receive<M: Decodable>(read_handle: oak::ReadHandle) -> Result<M> {
    let mut bytes = Vec::<u8>::with_capacity(512);
    let mut handles = Vec::with_capacity(2);
    match oak::channel_read(read_handle, &mut bytes, &mut handles) {
        Ok(()) => {
            let msg: M = M::decode(&bytes, &handles).context("could not decode message")?;
            Ok(msg)
        }
        Err(status) => {
            // TODO(#457): Propagate error code to caller.
            Err(anyhow!("could not read from channel: {:?}", status))
        }
    }
}
