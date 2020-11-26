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
    io::{Receiver, ReceiverExt, Sender, SenderExt},
    proto::oak::invocation::HttpInvocation,
    OakError,
};
use log::error;
use oak_abi::label::Label;
use oak_services::proto::oak::encap::{HttpRequest, HttpResponse};

/// A pair of temporary channels to pass the HTTP request to the HTTP Client and receive the
/// response.
pub struct Pipe {
    http_invocation: HttpInvocation,
    pub request_writer: Sender<HttpRequest>,
    pub response_reader: Receiver<HttpResponse>,
}

impl Pipe {
    pub fn new(request_label: &Label, response_label: &Label) -> Result<Self, OakError> {
        // Create a channel for passing HTTP requests to the HTTP Client node.
        let (request_writer, request_reader) =
            crate::io::channel_create("HTTP request", request_label)?;

        let (response_writer, response_reader) =
            crate::io::channel_create("HTTP response", response_label)?;

        let http_invocation = HttpInvocation {
            receiver: Some(request_reader),
            sender: Some(response_writer),
        };

        Ok(Pipe {
            http_invocation,
            request_writer,
            response_reader,
        })
    }

    /// Inserts the incoming HTTP request in the `request channel` part of the `HttpInvocation`.
    pub fn insert_message(&self, request: HttpRequest) -> Result<(), OakError> {
        // Put the HTTP request message inside the per-invocation request channel.
        self.request_writer.send(&request)
    }

    /// Sends the `HttpInvocation` with request and response channels on the invocation_channel.
    pub fn send_invocation(
        &self,
        invocation_channel: &oak_io::Sender<HttpInvocation>,
    ) -> Result<(), OakError> {
        // Send the invocation containing request-specific channels.
        invocation_channel.send(&self.http_invocation)
    }

    pub fn get_response(&self) -> Result<HttpResponse, OakError> {
        self.response_reader.receive()
    }

    /// Close all local handles except for the one that allows reading responses.
    pub fn close(self) {
        if let Err(err) = self.request_writer.close() {
            error!(
                "Failed to close request writer channel for invocation: {:?}",
                err
            );
        }
        if let Err(err) = self.response_reader.close() {
            error!(
                "Failed to close response reader channel for invocation: {:?}",
                err
            );
        }
        self.http_invocation.close();
    }
}

impl HttpInvocation {
    fn close(self) {
        if let Err(err) = self
            .receiver
            .ok_or(oak_abi::OakStatus::ErrBadHandle)
            .and_then(|receiver| receiver.close())
        {
            error!(
                "Failed to close request reader channel for invocation: {:?}",
                err
            );
        }
        if let Err(err) = self
            .sender
            .ok_or(oak_abi::OakStatus::ErrBadHandle)
            .and_then(|sender| sender.close())
        {
            error!(
                "Failed to close response writer channel for invocation: {:?}",
                err
            );
        }
    }
}
