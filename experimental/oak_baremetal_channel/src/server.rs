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

use crate::{InvocationChannel, Message, Vec};
use ciborium_io::{Read, Write};

pub struct ServerChannelHandle<T: Read + Write> {
    inner: InvocationChannel<T>,
}

impl<T> ServerChannelHandle<T>
where
    T: Read<Error = anyhow::Error> + Write<Error = anyhow::Error>,
{
    pub fn new(socket: T) -> Self {
        Self {
            inner: InvocationChannel::new(socket),
        }
    }
    pub fn read_request(&mut self) -> anyhow::Result<Message> {
        let message = self.inner.read_message()?;
        Ok(message)
    }
    pub fn write_response(&mut self, response: Message) -> anyhow::Result<()> {
        self.inner.write_message(response.into())
    }
}

/// Construct a [`oak_idl::Request`] from a [`Message`].
impl<'a> From<&'a Message> for oak_idl::Request<'a> {
    fn from(frame: &'a Message) -> Self {
        oak_idl::Request {
            method_id: frame.method_or_status,
            body: &frame.body,
        }
    }
}

/// Construct a [`Message`] from an response to an [`oak_idl::Request`].
impl From<Result<Vec<u8>, oak_idl::Status>> for Message {
    fn from(result: Result<Vec<u8>, oak_idl::Status>) -> Message {
        match result {
            Ok(response) => Message {
                method_or_status: oak_idl::StatusCode::Ok.into(),
                body: response,
            },
            Err(error) => Message {
                method_or_status: error.code.into(),
                body: error.message.as_bytes().to_vec(),
            },
        }
    }
}
