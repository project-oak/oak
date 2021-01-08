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

//! Functionality to help Oak Nodes create HTTP server and HTTP client pseudo-Nodes.

use crate::{
    io::{ReceiverExt, SenderExt},
    OakError, OakStatus,
};
use http::{Request, Response};
use log::warn;
use oak_abi::label::Label;
pub use oak_services::proto::oak::encap::{HeaderMap, HttpRequest, HttpResponse};
use std::convert::TryInto;

pub use crate::proto::oak::invocation::{HttpInvocation, HttpInvocationSource};

pub mod client;
pub mod server;

/// This implementation provides an interface for receiving requests and sending responses, using
/// the idiomatic http types. Internally, these types are converted into Protobuf encoded requests
/// and responses that can be used for communication with the Oak nodes.
impl HttpInvocation {
    pub fn receive(&self) -> Result<Request<Vec<u8>>, crate::OakError> {
        let request = self
            .receiver
            .as_ref()
            .ok_or(OakError::OakStatus(OakStatus::ErrBadHandle))?
            .receive();

        request.and_then(|req| req.try_into().map_err(crate::OakError::OakStatus))
    }

    pub fn send(&self, response: &Response<Vec<u8>>) -> Result<(), crate::OakError> {
        let response = HttpResponse::from(response);
        self.sender
            .as_ref()
            .ok_or(OakError::OakStatus(OakStatus::ErrBadHandle))?
            .send(&response)
    }

    pub fn close_channels(&self) {
        match self.receiver.as_ref() {
            Some(receiver) => {
                if let Err(error) = receiver.close() {
                    warn!("Error when trying to close receiver: {}", error);
                }
            }
            None => warn!("No receive present on invocation."),
        };
        match self.sender.as_ref() {
            Some(sender) => {
                if let Err(error) = sender.close() {
                    warn!("Error when trying to close response_sender: {}", error);
                }
            }
            None => warn!("No receive present on invocation."),
        };
    }
}

impl Drop for HttpInvocation {
    fn drop(&mut self) {
        self.close_channels();
    }
}

/// This implementation provides an interface for sending requests and receiving responses, using
/// the idiomatic http types. Internally, these types are converted into Protobuf encoded requests
/// and responses that can be used for communication with the Oak nodes.
/// It is a dual implementation to `HttpInvocation` and represents a sender part of the invocation.
impl HttpInvocationSource {
    pub fn receive(&self) -> Result<Response<Vec<u8>>, crate::OakError> {
        let response = self
            .receiver
            .as_ref()
            .ok_or(OakError::OakStatus(OakStatus::ErrBadHandle))?
            .receive();

        response.and_then(|req| req.try_into().map_err(crate::OakError::OakStatus))
    }

    pub fn send(&self, request: Request<Vec<u8>>) -> Result<(), crate::OakError> {
        let request = HttpRequest::from(request);
        self.sender
            .as_ref()
            .ok_or(OakError::OakStatus(OakStatus::ErrBadHandle))?
            .send(&request)
    }

    pub fn close_channels(&self) {
        match self.receiver.as_ref() {
            Some(receiver) => {
                if let Err(error) = receiver.close() {
                    warn!("Error when trying to close receiver: {}", error);
                }
            }
            None => warn!("No receive present on invocation."),
        };
        match self.sender.as_ref() {
            Some(sender) => {
                if let Err(error) = sender.close() {
                    warn!("Error when trying to close response_sender: {}", error);
                }
            }
            None => warn!("No receive present on invocation."),
        };
    }
}

impl Drop for HttpInvocationSource {
    fn drop(&mut self) {
        self.close_channels();
    }
}

/// Creates an `HttpInvocation` and a corresponding `HttpInvocationSource`.
pub fn create_http_invocation(
    label: &Label,
) -> Result<(HttpInvocation, HttpInvocationSource), OakStatus> {
    // Create a channel for passing HTTP requests.
    let (request_sender, request_receiver) = crate::io::channel_create("HTTP request", label)?;
    // Create a channel for collecting HTTP responses.
    let (response_sender, response_receiver) = crate::io::channel_create("HTTP response", label)?;

    Ok((
        HttpInvocation {
            receiver: Some(request_receiver),
            sender: Some(response_sender),
        },
        HttpInvocationSource {
            sender: Some(request_sender),
            receiver: Some(response_receiver),
        },
    ))
}
