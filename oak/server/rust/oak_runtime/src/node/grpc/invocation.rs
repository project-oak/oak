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

use crate::{
    io::{Decodable, Receiver, Sender},
    runtime::RuntimeProxy,
    NodeMessage,
};
use log::error;
use oak_abi::{
    proto::oak::encap::{GrpcRequest, GrpcResponse},
    OakStatus,
};

/// A gRPC invocation, consisting of exactly two channels: one to read incoming requests from the
/// client (wrapped in a [`Receiver`]), and one to write outgoing responses to the client (wrapped
/// in a [`Sender`]).
pub struct Invocation {
    receiver: Receiver<GrpcRequest>,
    sender: Sender<GrpcResponse>,
}

impl Decodable for Invocation {
    fn decode(message: &NodeMessage) -> Result<Self, OakStatus> {
        if !message.data.is_empty() {
            error!("Non-empty data field");
            return Err(OakStatus::ErrInternal);
        }
        if message.handles.len() != 2 {
            error!(
                "Incorrect number of handles received: {} (expected: 2)",
                message.handles.len()
            );
            return Err(OakStatus::ErrInternal);
        }
        Ok(Self {
            receiver: Receiver::new(message.handles[0]),
            sender: Sender::new(message.handles[1]),
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
    pub fn receive_request(&self, runtime: &RuntimeProxy) -> Result<GrpcRequest, OakStatus> {
        self.receiver.receive(runtime)
    }

    pub fn send_response(
        &self,
        response: GrpcResponse,
        runtime: &RuntimeProxy,
    ) -> Result<(), OakStatus> {
        self.sender.send(response, runtime)
    }
    /// Send an error response for the invocation.
    pub fn send_error(
        &self,
        code: oak_abi::proto::google::rpc::Code,
        msg: &str,
        runtime: &RuntimeProxy,
    ) {
        error!("Fail invocation with {:?} '{}'", code, msg);
        let _ = self.sender.send(
            GrpcResponse {
                rsp_msg: vec![],
                status: Some(oak_abi::proto::google::rpc::Status {
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
