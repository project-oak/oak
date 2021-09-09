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
    io::{channel_create_with_downgrade, Receiver, ReceiverExt, Sender, SenderExt},
    proto::oak::invocation::HttpInvocation,
    RuntimeProxy,
};
use anyhow::Context;
use log::error;
use oak_abi::label::Label;
use oak_io::handle::WriteHandle;
use oak_services::proto::oak::encap::{HttpRequest, HttpResponse};

/// A pair of temporary channels to pass the HTTP request to the Oak Node and receive the response.
pub struct Pipe {
    pub request_sender: Sender<HttpRequest>,
    pub request_receiver: Receiver<HttpRequest>,
    pub response_sender: Sender<HttpResponse>,
    pub response_receiver: Receiver<HttpResponse>,
}

impl Pipe {
    pub fn new(
        runtime: &RuntimeProxy,
        request_label: &Label,
        user_identity_label: &Label,
    ) -> anyhow::Result<Self> {
        // Create a channel for passing HTTP requests to the Oak node. This channel is created with
        // the label specified by the caller. Without a `public_fully_trusted` label or a privilege
        // that allows removing integrity tags, this will fail if the label has a non-empty
        // integrity component.
        let (request_sender, request_receiver) =
            channel_create_with_downgrade(runtime, "HTTP request", request_label)?;

        let (response_sender, response_receiver) =
            channel_create_with_downgrade(runtime, "HTTP response", user_identity_label)?;

        Ok(Pipe {
            request_sender,
            request_receiver,
            response_sender,
            response_receiver,
        })
    }

    /// Inserts the incoming HTTP request in the `request channel` part of the `HttpInvocation`.
    pub fn insert_message(
        &self,
        runtime: &RuntimeProxy,
        request: HttpRequest,
    ) -> anyhow::Result<()> {
        // Put the HTTP request message inside the per-invocation request channel.
        self.request_sender
            .send_with_downgrade(request, runtime)
            .context("Couldn't write the request to the HTTP request channel")
    }

    /// Sends the `HttpInvocation` with request and response channels to the Oak Node.
    pub fn send_invocation(
        &self,
        runtime: &RuntimeProxy,
        invocation_channel: WriteHandle,
    ) -> anyhow::Result<()> {
        // Create an invocation containing request-specific channels.
        let invocation = HttpInvocation {
            receiver: Some(self.request_receiver.clone()),
            sender: Some(self.response_sender.clone()),
        };
        let invocation_sender = crate::io::Sender::new(invocation_channel);
        invocation_sender
            .send_with_downgrade(invocation, runtime)
            .context("Couldn't write the invocation message")
    }

    /// Close all local handles except for the one that allows reading responses.
    pub fn close(self, runtime: &RuntimeProxy) {
        if let Err(err) = self.request_sender.close(runtime) {
            error!(
                "Failed to close request sender channel for invocation: {:?}",
                err
            );
        }
        if let Err(err) = self.request_receiver.close(runtime) {
            error!(
                "Failed to close request receiver channel for invocation: {:?}",
                err
            );
        }
        if let Err(err) = self.response_sender.close(runtime) {
            error!(
                "Failed to close response sender channel for invocation: {:?}",
                err
            );
        }
    }
}
