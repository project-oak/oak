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

//! Functionality for handling gRPC and HTTP invocations.

pub use crate::proto::oak::invocation::{GrpcInvocation, HttpInvocation};
use crate::{
    io::{ReceiverExt, SenderExt},
    RuntimeProxy,
};
use log::error;
use oak_abi::OakStatus;
use oak_io::OakError;
use oak_services::proto::oak::encap::{GrpcRequest, GrpcResponse, HttpRequest, HttpResponse};

pub trait InvocationExt {
    type Request: oak_io::handle::HandleVisit + oak_io::Decodable;
    type Response: oak_io::handle::HandleVisit + oak_io::Encodable;
    type ErrorCode: std::fmt::Debug;

    /// Returns the receiver part of this invocation.
    fn receiver(&self) -> &Option<oak_io::Receiver<Self::Request>>;

    /// Returns the sender part of the this invocation.
    fn sender(&self) -> &Option<oak_io::Sender<Self::Response>>;

    /// Creates a response from a given error code, and error message.
    fn encap_error(&self, code: Self::ErrorCode, msg: &str) -> Self::Response;

    /// Closes the channels used by the sender and receiver fields.
    ///
    /// Any errors while trying to close the sender or receive are logged, but otherwise ignored.
    #[cfg(not(feature = "linear-handles"))]
    fn close(&self, runtime: &RuntimeProxy) {
        match self.receiver() {
            Some(receiver) => {
                let receiver = oak_io::Receiver::<Self::Request>::new(receiver.handle);
                if let Err(err) = receiver.close(runtime) {
                    error!("Failed to close receiver channel in invocation: {:?}", err);
                }
            }
            None => error!("No receiver on invocation."),
        };
        match self.sender() {
            Some(sender) => {
                let sender = oak_io::Sender::<Self::Response>::new(sender.handle);
                if let Err(err) = sender.close(runtime) {
                    error!("Failed to close sender channel in invocation: {:?}", err);
                }
            }
            None => error!("No sender on invocation."),
        };
    }

    /// This function does nothing if the `linear-handles` feature is enabled, sender and receiver
    /// are `Drop`ed automatically. We only include this definition to keep the same trait
    /// definition with or without `linear-handles` enabled.
    #[cfg(feature = "linear-handles")]
    fn close(&self, _runtime: &RuntimeProxy) {
        // Do nothing
    }

    fn receive_request(&self, runtime: &RuntimeProxy) -> Result<Self::Request, OakError> {
        match &self.receiver() {
            Some(receiver) => receiver.receive(runtime),
            None => Err(OakError::OakStatus(OakStatus::ErrBadHandle)),
        }
    }

    fn send_response(
        &self,
        response: Self::Response,
        runtime: &RuntimeProxy,
    ) -> Result<(), OakError> {
        match &self.sender() {
            Some(sender) => sender.send(response, runtime),
            None => Err(OakError::OakStatus(OakStatus::ErrBadHandle)),
        }
    }

    /// Send an error response for the invocation.
    fn send_error(&self, code: Self::ErrorCode, msg: &str, runtime: &RuntimeProxy) {
        error!("Fail invocation with {:?} '{}'", code, msg);
        let _ = self.send_response(self.encap_error(code, msg), runtime);
    }
}

impl InvocationExt for GrpcInvocation {
    type Request = GrpcRequest;
    type Response = GrpcResponse;
    type ErrorCode = oak_services::proto::google::rpc::Code;

    fn receiver(&self) -> &Option<oak_io::Receiver<Self::Request>> {
        &self.receiver
    }

    fn sender(&self) -> &Option<oak_io::Sender<Self::Response>> {
        &self.sender
    }

    fn encap_error(&self, code: Self::ErrorCode, msg: &str) -> Self::Response {
        GrpcResponse {
            rsp_msg: vec![],
            status: Some(oak_services::proto::google::rpc::Status {
                code: code as i32,
                message: msg.to_string(),
                details: vec![],
            }),
            last: true,
        }
    }
}

impl InvocationExt for HttpInvocation {
    type Request = HttpRequest;
    type Response = HttpResponse;
    type ErrorCode = http::StatusCode;

    fn receiver(&self) -> &Option<oak_io::Receiver<Self::Request>> {
        &self.receiver
    }

    fn sender(&self) -> &Option<oak_io::Sender<Self::Response>> {
        &self.sender
    }

    fn encap_error(&self, code: Self::ErrorCode, msg: &str) -> Self::Response {
        HttpResponse {
            body: msg.as_bytes().to_vec(),
            status: code.as_u16() as i32,
            headers: None,
        }
    }
}
