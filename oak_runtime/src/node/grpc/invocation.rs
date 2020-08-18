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

//! Functionality for handling gRPC method invocations.

use crate::{
    io::{Receiver, ReceiverExt, Sender, SenderExt},
    NodeMessage, RuntimeProxy,
};
use log::error;
use oak_abi::OakStatus;
use oak_io::OakError;
use oak_io::{
    handle::{ReadHandle, WriteHandle},
    Decodable,
};
use oak_services::proto::oak::encap::{GrpcRequest, GrpcResponse};

/// A gRPC invocation, consisting of exactly two channels: one to read incoming requests from the
/// client (wrapped in a [`Receiver`]), and one to write outgoing responses to the client (wrapped
/// in a [`Sender`]).
pub struct Invocation {
    receiver: Receiver<GrpcRequest>,
    sender: Sender<GrpcResponse>,
}

impl Decodable for Invocation {
    fn decode(message: &NodeMessage) -> Result<Self, OakError> {
        if !message.bytes.is_empty() {
            error!("Non-empty data field");
            return Err(OakStatus::ErrInternal.into());
        }
        if message.handles.len() != 2 {
            error!(
                "Incorrect number of handles received: {} (expected: 2)",
                message.handles.len()
            );
            return Err(OakStatus::ErrInternal.into());
        }
        Ok(Self {
            receiver: Receiver::new(ReadHandle {
                handle: message.handles[0],
            }),
            sender: Sender::new(WriteHandle {
                handle: message.handles[1],
            }),
        })
    }
}

impl Invocation {
    pub fn close(self, runtime: &RuntimeProxy) {
        if let Err(err) = self.receiver.close(runtime) {
            error!("Failed to close receiver channel in invocation: {:?}", err);
        }
        if let Err(err) = self.sender.close(runtime) {
            error!("Failed to close sender channel in invocation: {:?}", err);
        }
    }
    pub fn receive_request(&self, runtime: &RuntimeProxy) -> Result<GrpcRequest, OakError> {
        self.receiver.receive(runtime)
    }

    pub fn send_response(
        &self,
        response: GrpcResponse,
        runtime: &RuntimeProxy,
    ) -> Result<(), OakError> {
        self.sender.send(response, runtime)
    }
    /// Send an error response for the invocation.
    pub fn send_error(
        &self,
        code: oak_services::proto::google::rpc::Code,
        msg: &str,
        runtime: &RuntimeProxy,
    ) {
        error!("Fail invocation with {:?} '{}'", code, msg);
        let _ = self.sender.send(
            GrpcResponse {
                rsp_msg: vec![],
                status: Some(oak_services::proto::google::rpc::Status {
                    code: code as i32,
                    message: msg.to_string(),
                    details: vec![],
                }),
                last: true,
            },
            runtime,
        );
    }
}
