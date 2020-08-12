//
// Copyright 2020 The Project Oak Authors
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

use crate::io::{ReceiverExt, SenderExt};
use log::warn;

/// An invocation, consisting of exactly two channels: one to read incoming requests from the
/// client, and one to write outgoing responses to the client.
pub struct Invocation<R: crate::io::Decodable, S: crate::io::Encodable> {
    pub request_receiver: crate::io::Receiver<R>,
    pub response_sender: crate::io::Sender<S>,
}

// TODO(#389): Automatically generate this code.
impl<R: crate::io::Decodable, S: crate::io::Encodable> crate::io::Encodable for Invocation<R, S> {
    fn encode(&self) -> Result<crate::io::Message, crate::OakError> {
        let bytes = vec![];
        let handles = vec![
            self.request_receiver.handle.handle,
            self.response_sender.handle.handle,
        ];
        Ok(crate::io::Message { bytes, handles })
    }
}

// TODO(#389): Automatically generate this code.
impl<R: crate::io::Decodable, S: crate::io::Encodable> crate::io::Decodable for Invocation<R, S> {
    fn decode(message: &crate::io::Message) -> Result<Self, crate::OakError> {
        if !message.bytes.is_empty() {
            panic!(
                "incorrect number of bytes received: {} (expected: 0)",
                message.bytes.len()
            );
        }
        if message.handles.len() != 2 {
            panic!(
                "incorrect number of handles received: {} (expected: 2)",
                message.handles.len()
            );
        }
        Ok(Invocation {
            request_receiver: crate::io::Receiver::new(crate::ReadHandle {
                handle: message.handles[0],
            }),
            response_sender: crate::io::Sender::new(crate::WriteHandle {
                handle: message.handles[1],
            }),
        })
    }
}

impl<R: crate::io::Decodable, S: crate::io::Encodable> Invocation<R, S> {
    pub fn receive(&self) -> Result<R, crate::OakError> {
        self.request_receiver.receive()
    }

    pub fn send(&self, response: &S) -> Result<(), crate::OakError> {
        self.response_sender.send(response)
    }

    pub fn close_channels(&self) {
        if let Err(error) = self.request_receiver.close() {
            warn!("Error when trying to close request_receiver: {}", error);
        }
        if let Err(error) = self.response_sender.close() {
            warn!("Error when trying to close response_sender: {}", error);
        }
    }
}

/// Wrapper for a sender that can be used to send invocations to an Oak node that will handle the
/// requests.
pub struct ServerInvocationChannel<R: crate::io::Decodable, S: crate::io::Encodable> {
    invocation_sender: crate::io::Sender<Invocation<R, S>>,
}

impl<R: crate::io::Decodable, S: crate::io::Encodable> ServerInvocationChannel<R, S> {
    pub fn new(invocation_sender: crate::io::Sender<Invocation<R, S>>) -> Self {
        ServerInvocationChannel { invocation_sender }
    }
}

// TODO(#389): Automatically generate this code.
impl<R: crate::io::Decodable, S: crate::io::Encodable> crate::io::Encodable
    for ServerInvocationChannel<R, S>
{
    fn encode(&self) -> Result<crate::io::Message, crate::OakError> {
        let bytes = vec![];
        let handles = vec![self.invocation_sender.handle.handle];
        Ok(crate::io::Message { bytes, handles })
    }
}

// TODO(#389): Automatically generate this code.
impl<R: crate::io::Decodable, S: crate::io::Encodable> crate::io::Decodable
    for ServerInvocationChannel<R, S>
{
    fn decode(message: &crate::io::Message) -> Result<Self, crate::OakError> {
        if !message.bytes.is_empty() {
            panic!(
                "incorrect number of bytes received: {} (expected: 0)",
                message.bytes.len()
            );
        }
        if message.handles.len() != 1 {
            panic!(
                "incorrect number of handles received: {} (expected: 1)",
                message.handles.len()
            );
        }
        Ok(ServerInvocationChannel {
            invocation_sender: crate::io::Sender::new(crate::WriteHandle {
                handle: message.handles[0],
            }),
        })
    }
}
