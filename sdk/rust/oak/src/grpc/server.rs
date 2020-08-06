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

//! Functionality to help Oak Nodes create gRPC server pseudo-Nodes.

use crate::{
    grpc::Invocation,
    io::{Receiver, ReceiverExt, SenderExt},
    OakStatus,
};

struct GrpcServerInit {
    invocation_sender: crate::io::Sender<Invocation>,
}

// TODO(#389): Automatically generate this code.
impl crate::io::Encodable for GrpcServerInit {
    fn encode(&self) -> Result<crate::io::Message, crate::OakError> {
        let bytes = vec![];
        let handles = vec![self.invocation_sender.handle.handle];
        Ok(crate::io::Message { bytes, handles })
    }
}

// TODO(#389): Automatically generate this code.
impl crate::io::Decodable for GrpcServerInit {
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
        Ok(GrpcServerInit {
            invocation_sender: crate::io::Sender::new(crate::WriteHandle {
                handle: message.handles[0],
            }),
        })
    }
}

/// Initializes a gRPC server pseudo-Node listening on the provided address.
///
/// Returns a [`Receiver`] to read gRPC [`Invocation`]s from.
pub fn init(address: &str) -> Result<Receiver<Invocation>, OakStatus> {
    // Create a channel and pass the read half to a new gRPC server pseudo-Node.
    let (init_sender, init_receiver) = crate::io::channel_create::<GrpcServerInit>()
        .expect("Couldn't create init channel to gRPC server pseudo-node");
    let config = crate::node_config::grpc_server(address);
    crate::node_create(&config, init_receiver.handle)?;
    init_receiver
        .close()
        .expect("Couldn't close init channel to gRPC server pseudo-node");

    // Create a separate channel for receiving invocations and pass it to a gRPC pseudo-Node.
    let (invocation_sender, invocation_receiver) =
        crate::io::channel_create::<Invocation>().expect("Couldn't create gRPC invocation channel");

    let grpc_server_init = GrpcServerInit { invocation_sender };
    init_sender
        .send(&grpc_server_init)
        .expect("Could not send init message to gRPC server pseudo-node");
    init_sender
        .close()
        .expect("Couldn't close init message channel to gRPC server pseudo-node");

    Ok(invocation_receiver)
}
