//
// Copyright 2022 The Project Oak Authors
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

use crate::{InvocationChannel, Message, String, Vec};
use ciborium_io::{Read, Write};

pub struct ClientChannelHandle<T: Read + Write> {
    inner: InvocationChannel<T>,
}

impl<T> ClientChannelHandle<T>
where
    T: Read<Error = anyhow::Error> + Write<Error = anyhow::Error>,
{
    pub fn new(socket: T) -> Self {
        Self {
            inner: InvocationChannel::new(socket),
        }
    }
    pub fn write_request(&mut self, request: Message) -> anyhow::Result<()> {
        self.inner.write_message(request.into())
    }
    pub fn read_response(&mut self) -> anyhow::Result<Message> {
        let message = self.inner.read_message()?;
        Ok(message.into())
    }
}

/// Construct a [`Message`] from an [`oak_idl::Request`].
impl<'a> From<oak_idl::Request<'a>> for Message {
    fn from(request: oak_idl::Request) -> Message {
        Message {
            method_or_status: request.method_id,
            // TODO(#2848): It'd be nice if we didn't have to reallocate here.
            // We may be able to avoid doing so by making [`Message`] use
            // slices and lifetimes. Or alternatively use the Bytes crate for
            // reference counting.
            body: request.body.to_vec(),
        }
    }
}

/// Construct the response to a [`oak_idl::Request`] from a [`Message`].
impl From<Message> for Result<Vec<u8>, oak_idl::Status> {
    fn from(frame: Message) -> Self {
        if frame.method_or_status == oak_idl::StatusCode::Ok.into() {
            Ok(frame.body)
        } else {
            Err(oak_idl::Status {
                code: frame.method_or_status.into(),
                message: String::from_utf8(frame.body.to_vec()).unwrap_or_else(|err| {
                    alloc::format!(
                        "Could not parse response error message bytes as utf8: {:?}",
                        err
                    )
                }),
            })
        }
    }
}
