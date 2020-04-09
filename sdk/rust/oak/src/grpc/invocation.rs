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

/// A gRPC invocation, consisting of exactly two channels: one to read incoming requests from the
/// client, and one to write outgoing responses to the client.
pub struct Invocation {
    pub request_receiver: crate::io::Receiver<oak_abi::proto::oak::encap::GrpcRequest>,
    pub response_sender: crate::io::Sender<oak_abi::proto::oak::encap::GrpcResponse>,
}

// TODO(#389): Automatically generate this code.
impl crate::io::Encodable for Invocation {
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
impl crate::io::Decodable for Invocation {
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
