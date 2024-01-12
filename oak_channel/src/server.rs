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

use anyhow::Context;
use oak_core::{samplestore::SampleStore, timer::Timer};

use crate::{message, Channel, InvocationChannel};

/// Starts a blocking server that listens for requests on the provided channel
/// and responds to them using the provided [`micro_rpc::Transport`].
pub fn start_blocking_server<T: micro_rpc::Transport<Error = !>>(
    channel: Box<dyn Channel>,
    mut server: T,
    stats: &mut dyn SampleStore,
) -> anyhow::Result<!> {
    let channel_handle = &mut ServerChannelHandle::new(channel);
    loop {
        log::debug!("waiting for a request message");
        let (request_message, timer) = channel_handle
            .read_request()
            .context("couldn't receive message")?;
        let request_message_invocation_id = request_message.invocation_id;
        log::debug!(
            "received request message with invocation id {} ({} bytes)",
            request_message_invocation_id,
            request_message.body.len()
        );
        let response = server.invoke(request_message.body.as_ref()).into_ok();
        log::debug!(
            "sending response message with invocation id {} ({} bytes)",
            request_message_invocation_id,
            response.len()
        );
        let response_message = message::ResponseMessage {
            invocation_id: request_message_invocation_id,
            body: response,
        };
        channel_handle.write_response(response_message)?;
        stats.record(timer.elapsed());
    }
}

struct ServerChannelHandle {
    inner: InvocationChannel,
}

impl ServerChannelHandle {
    pub fn new(socket: Box<dyn Channel>) -> Self {
        Self {
            inner: InvocationChannel::new(socket),
        }
    }
    pub fn read_request(&mut self) -> anyhow::Result<(message::RequestMessage, Timer)> {
        self.inner.read_message()
    }

    pub fn write_response(&mut self, response: message::ResponseMessage) -> anyhow::Result<()> {
        self.inner.write_message(response)
    }
}
