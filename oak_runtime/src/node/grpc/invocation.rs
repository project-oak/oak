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

pub use crate::proto::oak::invocation::GrpcInvocation as Invocation;
use crate::{
    io::{ReceiverExt, SenderExt},
    RuntimeProxy,
};
use log::error;
use oak_abi::OakStatus;
use oak_io::OakError;
use oak_services::proto::oak::encap::{GrpcRequest, GrpcResponse};

impl Invocation {
    /// Closes the channels used by the sender and receiver fields.
    ///
    /// Any errors while trying to close the sender or receive are logged, but otherwise ignored.
    pub fn close(self, runtime: &RuntimeProxy) {
        match self.receiver {
            Some(receiver) => {
                if let Err(err) = receiver.close(runtime) {
                    error!("Failed to close receiver channel in invocation: {:?}", err);
                }
            }
            None => error!("No receiver on invocation."),
        };
        match self.sender {
            Some(sender) => {
                if let Err(err) = sender.close(runtime) {
                    error!("Failed to close sender channel in invocation: {:?}", err);
                }
            }
            None => error!("No sender on invocation."),
        };
    }

    pub fn receive_request(&self, runtime: &RuntimeProxy) -> Result<GrpcRequest, OakError> {
        match &self.receiver {
            Some(receiver) => receiver.receive(runtime),
            None => Err(OakError::OakStatus(OakStatus::ErrBadHandle)),
        }
    }

    pub fn send_response(
        &self,
        response: GrpcResponse,
        runtime: &RuntimeProxy,
    ) -> Result<(), OakError> {
        match &self.sender {
            Some(sender) => sender.send(response, runtime),
            None => Err(OakError::OakStatus(OakStatus::ErrBadHandle)),
        }
    }

    /// Send an error response for the invocation.
    pub fn send_error(
        &self,
        code: oak_services::proto::google::rpc::Code,
        msg: &str,
        runtime: &RuntimeProxy,
    ) {
        error!("Fail invocation with {:?} '{}'", code, msg);
        let _ = self.send_response(
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
