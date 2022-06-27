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

extern crate alloc;

use crate::{
    message::{InvocationId, RequestMessage, ResponseMessage},
    Channel, InvocationChannel,
};
use alloc::{string::String, vec::Vec};

pub struct ClientChannelHandle<T: Channel> {
    inner: InvocationChannel<T>,
}

impl<T> ClientChannelHandle<T>
where
    T: Channel,
{
    pub fn new(socket: T) -> Self {
        Self {
            inner: InvocationChannel::new(socket),
        }
    }
    pub fn write_request(&mut self, request: RequestMessage) -> anyhow::Result<()> {
        self.inner.write_message(request)
    }
    pub fn read_response(&mut self) -> anyhow::Result<ResponseMessage> {
        let message = self.inner.read_message()?;
        Ok(message)
    }
}

#[derive(Default)]
pub struct RequestEncoder {
    invocation_id_counter: InvocationIdCounter,
}

impl RequestEncoder {
    pub fn encode_request(&mut self, request: oak_idl::Request) -> RequestMessage {
        let invocation_id = self.invocation_id_counter.next_invocation_id();
        RequestMessage {
            invocation_id,
            method_id: request.method_id,
            body: request.body.to_vec(),
        }
    }
}

#[derive(Default)]
struct InvocationIdCounter {
    next_invocation_id: InvocationId,
}

impl InvocationIdCounter {
    fn next_invocation_id(&mut self) -> InvocationId {
        let next_invocation_id = self.next_invocation_id;
        self.next_invocation_id = next_invocation_id.wrapping_add(1);
        next_invocation_id
    }
}

/// Construct the response to a [`oak_idl::Request`] from a [`ResponseMessage`].
impl From<ResponseMessage> for Result<Vec<u8>, oak_idl::Status> {
    fn from(message: ResponseMessage) -> Self {
        if message.status_code == oak_idl::StatusCode::Ok.into() {
            Ok(message.body)
        } else {
            Err(oak_idl::Status {
                code: message.status_code.into(),
                message: String::from_utf8(message.body.to_vec()).unwrap_or_else(|err| {
                    alloc::format!(
                        "Could not parse response error message bytes as utf8: {:?}",
                        err
                    )
                }),
            })
        }
    }
}
