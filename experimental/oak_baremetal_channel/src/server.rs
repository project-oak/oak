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

use crate::{message, Channel, InvocationChannel, Vec};
use alloc::boxed::Box;

pub struct ServerChannelHandle {
    inner: InvocationChannel,
}

impl ServerChannelHandle {
    pub fn new(socket: Box<dyn Channel>) -> Self {
        Self {
            inner: InvocationChannel::new(socket),
        }
    }
    pub fn read_request(&mut self) -> anyhow::Result<message::RequestMessage> {
        let message = self.inner.read_message()?;
        Ok(message)
    }
    pub fn write_response(&mut self, response: message::ResponseMessage) -> anyhow::Result<()> {
        self.inner.write_message(response)
    }
}

/// Construct a [`oak_idl::Request`] from a [`message::RequestMessage`].
impl From<message::RequestMessage> for oak_idl::Request {
    fn from(message: message::RequestMessage) -> Self {
        oak_idl::Request {
            method_id: message.method_id,
            body: message.body,
        }
    }
}

pub fn message_from_response_and_id(
    response: Result<Vec<u8>, oak_idl::Status>,
    invocation_id: message::InvocationId,
) -> message::ResponseMessage {
    match response {
        Ok(response) => message::ResponseMessage {
            invocation_id,
            status_code: oak_idl::StatusCode::Ok.into(),
            body: response,
        },
        Err(error) => message::ResponseMessage {
            invocation_id,
            status_code: error.code.into(),
            body: error.message.as_bytes().to_vec(),
        },
    }
}
