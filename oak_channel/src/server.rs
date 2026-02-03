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

use alloc::boxed::Box;

use oak_core::timer::Timer;

use crate::{Channel, InvocationChannel, message};

pub struct ServerChannelHandle {
    inner: InvocationChannel,
}

impl ServerChannelHandle {
    pub fn new(socket: Box<dyn Channel>) -> Self {
        Self { inner: InvocationChannel::new(socket) }
    }
    pub fn read_request(&mut self) -> anyhow::Result<(message::RequestMessage, Timer)> {
        self.inner.read_message()
    }

    pub fn write_response(&mut self, response: message::ResponseMessage) -> anyhow::Result<()> {
        self.inner.write_message(response)
    }
}
