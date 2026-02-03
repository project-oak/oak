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

use alloc::boxed::Box;

use oak_core::timer::Timer;

use crate::{
    Channel, InvocationChannel,
    message::{InvocationId, RequestMessage, ResponseMessage},
};

pub struct ClientChannelHandle {
    inner: InvocationChannel,
}

impl ClientChannelHandle {
    pub fn new(socket: Box<dyn Channel>) -> Self {
        Self { inner: InvocationChannel::new(socket) }
    }
    pub fn write_request(&mut self, request: RequestMessage) -> anyhow::Result<()> {
        self.inner.write_message(request)
    }

    pub fn read_response(&mut self) -> anyhow::Result<(ResponseMessage, Timer)> {
        self.inner.read_message()
    }
}

#[derive(Default)]
pub struct RequestEncoder {
    invocation_id_counter: InvocationIdCounter,
}

impl RequestEncoder {
    pub fn encode_request(&mut self, request_body: &[u8]) -> RequestMessage {
        let invocation_id = self.invocation_id_counter.next_invocation_id();
        RequestMessage { invocation_id, body: request_body.to_vec() }
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
