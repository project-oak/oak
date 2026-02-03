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

//! Provides functionality to communicate with host application over the
//! communication channel.

use alloc::boxed::Box;

use anyhow::{Context, anyhow};
use oak_channel::Channel;
pub use oak_channel::{Read, Write};
use oak_core::samplestore::SampleStore;
use oak_restricted_kernel_interface::OAK_CHANNEL_FD;

/// Channel that communicates over a file descriptor.
pub struct FileDescriptorChannel {
    fd: i32,
}

impl FileDescriptorChannel {
    pub fn new(fd: i32) -> Self {
        Self { fd }
    }
}

impl Default for FileDescriptorChannel {
    /// Constructs a new FileDescriptorChannel that assumes we'll use the
    /// well-known Oak file descriptor number.
    fn default() -> Self {
        Self::new(OAK_CHANNEL_FD)
    }
}

impl Read for FileDescriptorChannel {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let len = data.len();
        let mut remaining = data.len();

        while remaining > 0 {
            remaining -= oak_restricted_kernel_interface::syscall::read(
                self.fd,
                &mut data[len - remaining..],
            )
            .map_err(|err| anyhow!("read failure: {}", err))?;
        }

        Ok(())
    }
}

impl Write for FileDescriptorChannel {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let len = data.len();
        let mut remaining = data.len();

        while remaining > 0 {
            remaining -=
                oak_restricted_kernel_interface::syscall::write(self.fd, &data[len - remaining..])
                    .map_err(|err| anyhow!("write failure: {}", err))?;
        }

        Ok(())
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        oak_restricted_kernel_interface::syscall::fsync(self.fd)
            .map_err(|err| anyhow!("sync failure: {}", err))
    }
}

/// Starts a blocking server that listens for requests on the provided channel
/// and responds to them using the provided [`micro_rpc::Transport`].
pub fn start_blocking_server<T: micro_rpc::Transport<Error = !>>(
    channel: Box<dyn Channel>,
    mut server: T,
    stats: &mut dyn SampleStore,
) -> anyhow::Result<!> {
    let channel_handle = &mut oak_channel::server::ServerChannelHandle::new(channel);
    loop {
        log::debug!("waiting for a request message");
        let (request_message, timer) =
            channel_handle.read_request().context("couldn't receive message")?;
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
        let response_message = oak_channel::message::ResponseMessage {
            invocation_id: request_message_invocation_id,
            body: response,
        };
        channel_handle.write_response(response_message)?;
        stats.record(timer.elapsed());
    }
}
