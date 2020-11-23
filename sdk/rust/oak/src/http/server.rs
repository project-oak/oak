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
    proto::oak::invocation::HttpInvocationSender,
    OakStatus,
};
use oak_abi::label::Label;
pub use oak_services::proto::oak::encap::{HeaderMap, HttpRequest, HttpResponse};

pub type Invocation = crate::proto::oak::invocation::HttpInvocation;

/// Initializes an HTTP server pseudo-Node listening on the provided address.
///
/// Returns a [`Receiver`] to read HTTP [`Invocation`]s from.
pub fn init(address: &str) -> Result<Receiver<Invocation>, OakStatus> {
    // Create a separate channel for receiving invocations and pass it to a newly created HTTP
    // pseudo-Node.
    let (invocation_sender, invocation_receiver) =
        crate::io::channel_create::<Invocation>("HTTP invocation", &Label::public_untrusted())
            .expect("Couldn't create HTTP invocation channel");
    match init_with_sender(address, invocation_sender) {
        Ok(_) => {}
        Err(e) => {
            let _ = invocation_receiver.close();
            return Err(e);
        }
    };
    Ok(invocation_receiver)
}

/// Initializes an HTTP server pseudo-Node listening on the provided address.
///
/// Accepts a [`Sender`] of [`Invocation`] messages on which to send incoming HTTP invocations.
pub fn init_with_sender(
    address: &str,
    invocation_sender: Sender<Invocation>,
) -> Result<(), OakStatus> {
    let config = crate::node_config::http_server(address);
    // TODO(#1631): When we have a separate top for each sub-lattice, this should be changed to
    // the top of the identity sub-lattice.
    let top_label = oak_abi::label::confidentiality_label(oak_abi::label::top());
    // Create a channel and pass the read half to a new HTTP server pseudo-Node.
    let init_sender =
        match crate::io::node_create::<HttpInvocationSender>("http_server", &top_label, &config) {
            Ok(s) => s,
            Err(e) => {
                let _ = invocation_sender.close();
                return Err(e);
            }
        };

    let http_server_init = HttpInvocationSender {
        sender: Some(invocation_sender),
    };
    init_sender
        .send(&http_server_init)
        .expect("Could not send init message to HTTP server pseudo-node");
    init_sender
        .close()
        .expect("Couldn't close init message channel to HTTP server pseudo-node");
    http_server_init
        .sender
        .unwrap()
        .close()
        .expect("Couldn't close local copy of invocation sender channel");

    Ok(())
}
