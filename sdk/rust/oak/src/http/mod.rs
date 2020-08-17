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

//! Functionality to help Oak Nodes create HTTP server pseudo-Nodes.

use crate::{
    invocations::ServerInvocationChannel,
    io::{Receiver, ReceiverExt, SenderExt},
    OakStatus,
};
use oak_services::proto::oak::encap::{HttpRequest, HttpResponse};

pub type Invocation = crate::invocations::Invocation<HttpRequest, HttpResponse>;

/// Initializes an HTTP server pseudo-Node listening on the provided address.
///
/// Returns a [`Receiver`] to read HTTP [`Invocation`]s from.
pub fn init(address: &str) -> Result<Receiver<Invocation>, OakStatus> {
    let config = crate::node_config::http_server(address);

    // Create a channel and pass the read half to a new http server pseudo-Node.
    let (init_sender, init_receiver) =
        crate::io::channel_create::<ServerInvocationChannel<HttpRequest, HttpResponse>>()
            .expect("Couldn't create init channel to HTTP server pseudo-node");
    crate::node_create(&config, init_receiver.handle)?;
    init_receiver
        .close()
        .expect("Couldn't close init channel to HTTP server pseudo-node");

    // Create a separate channel for receiving invocations and pass it to an HTTP pseudo-Node.
    let (invocation_sender, invocation_receiver) =
        crate::io::channel_create::<Invocation>().expect("Couldn't create HTTP invocation channel");

    let http_server_init = ServerInvocationChannel::new(invocation_sender);
    init_sender
        .send(&http_server_init)
        .expect("Could not send init message to HTTP server pseudo-node");
    init_sender
        .close()
        .expect("Couldn't close init message channel to HTTP server pseudo-node");

    Ok(invocation_receiver)
}

impl crate::handle::HandleVisit for oak_services::proto::oak::encap::HttpRequest {
    fn visit<F: FnMut(&mut crate::Handle)>(&mut self, visitor: F) -> F {
        visitor
    }
}

impl crate::handle::HandleVisit for oak_services::proto::oak::encap::HttpResponse {
    fn visit<F: FnMut(&mut crate::Handle)>(&mut self, visitor: F) -> F {
        visitor
    }
}
