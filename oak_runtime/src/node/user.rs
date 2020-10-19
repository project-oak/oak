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

//! HTTP server pseudo-Node that can serve as a frontend for an Oak node.
//! The server receives requests from the outside, wraps each request in
//! an invocation and sends it to the designated Oak node to be processed
//! asynchronously.

use crate::{
    io::{Receiver, ReceiverExt, Sender, SenderExt},
    node::{ConfigurationError, Node, NodePrivilege},
    proto::oak::invocation::{HttpInvocation, InnerHttpInvocation},
    RuntimeProxy,
};
use log::{error, info, warn};
use oak_abi::{
    label::{Label, Tag, UserIdentityTag},
    proto::oak::application::UserNodeConfiguration,
};
use oak_io::handle::{ReadHandle, WriteHandle};
use oak_services::proto::oak::encap::HttpRequest;
use std::collections::HashSet;
use tokio::sync::oneshot;

/// Struct that represents a user node, with its privilege set to the user's identity.
pub struct UserNode {
    /// Pseudo-Node name.
    node_name: String,
    /// The privilege of the node.
    privilege: NodePrivilege,
}

impl UserNode {
    pub fn new(node_name: &str, config: UserNodeConfiguration) -> Result<Self, ConfigurationError> {
        let mut endorsement = HashSet::new();
        endorsement.insert(Tag {
            tag: Some(oak_abi::label::tag::Tag::UserIdentityTag(UserIdentityTag {
                public_key: config.privilege,
            })),
        });

        let privilege = NodePrivilege {
            can_declassify_confidentiality_tags: endorsement.clone(),
            can_endorse_integrity_tags: endorsement,
        };
        Ok(UserNode {
            node_name: node_name.to_string(),
            privilege,
        })
    }

    fn inject_http_request(
        &self,
        runtime: RuntimeProxy,
        inner_http_invocation: InnerHttpInvocation,
    ) -> Result<oak_abi::Handle, ()> {
        // Create a pair of temporary channels to pass the HTTP request and to receive the
        // response.
        let pipe = Pipe::new(
            &runtime,
            &inner_http_invocation.request_label.unwrap(),
            &self.privilege,
        )?;

        // Put the HTTP request message inside the per-invocation request channel.
        pipe.insert_message(&runtime, inner_http_invocation.request.unwrap())?;

        // Send an invocation message (with attached handles) to the Oak Node.
        pipe.send_invocation(
            &runtime,
            inner_http_invocation
                .invocation_sender
                .unwrap()
                .handle
                .handle,
        )?;

        // Close all local handles except for the one that allows reading responses.
        pipe.close(&runtime);

        Ok(pipe.response_reader)
    }
}

impl Node for UserNode {
    fn node_type(&self) -> &'static str {
        "user-node"
    }

    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        startup_handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        let receiver = Receiver::<InnerHttpInvocation>::new(ReadHandle {
            handle: startup_handle,
        });
        let inner_http_invocation = match receiver.receive(&runtime) {
            Ok(invocation) => invocation,
            Err(status) => {
                error!(
                    "{}: Failed to retrieve inner HTTP invocation: {:?}",
                    self.node_name, status
                );
                return;
            }
        };

        // Response-reader that contains the response. this should be handed to the HTTP node
        let response_reader =
            match self.inject_http_request(runtime.clone(), inner_http_invocation.clone()) {
                Ok(handle) => handle,
                Err(_) => return,
            };

        info!(
            "@@@@@@ injected the request, and received response handle: {}",
            response_reader
        );
        let response_receiver = crate::io::Receiver::new(ReadHandle {
            handle: response_reader,
        });

        info!("@@@@@@ Waiting on for the response to arrive");
        let response = match response_receiver.receive(&runtime) {
            Ok(rsp) => rsp,
            Err(err) => {
                error!(
                    "Could not receive the response from the Oak node on channel {}: {}.",
                    response_reader, err
                );
                return;
            }
        };

        info!("@@@@@@ Sending the response back to HTTP spn.");
        if let Err(err) = inner_http_invocation
            .response_sender
            .unwrap()
            .send(response, &runtime)
        {
            error!(
                "{}: Could not send response to HTTP server pseudo-node: {}",
                self.node_name, err,
            );
        };
    }

    fn get_privilege(&self) -> NodePrivilege {
        self.privilege.clone()
    }
}

/// A pair of temporary channels to pass the HTTP request and to receive the response.
struct Pipe {
    request_writer: oak_abi::Handle,
    request_reader: oak_abi::Handle,
    response_writer: oak_abi::Handle,
    response_reader: oak_abi::Handle,
}

impl Pipe {
    fn new(
        runtime: &RuntimeProxy,
        request_label: &Label,
        privilege: &NodePrivilege,
    ) -> Result<Self, ()> {
        // Create a channel for passing HTTP requests to the Oak node. This channel is created with
        // the label specified by the caller, and the identity of the caller.
        let request_reader_label = Label {
            confidentiality_tags: request_label.confidentiality_tags.clone(),
            integrity_tags: privilege
                .can_endorse_integrity_tags
                .clone()
                .into_iter()
                .collect(),
        };

        info!(
            "@@@@@@@@ Creating request_reader with {:?}",
            &request_reader_label
        );
        let (request_writer, request_reader) = runtime
            .channel_create(&request_reader_label)
            .map_err(|err| {
                warn!("could not create HTTP request channel: {:?}", err);
            })?;

        // Create a channel for receiving HTTP responses from the Oak node. This channel is created
        // with a label that has the identity of the caller as the confidentiality
        // component.
        let response_writer_label = Label {
            confidentiality_tags: privilege
                .can_endorse_integrity_tags
                .clone()
                .into_iter()
                .collect(),
            integrity_tags: vec![],
        };
        info!(
            "@@@@@@@@ Creating response_writer with {:?}",
            &response_writer_label
        );
        let (response_writer, response_reader) = runtime
            .channel_create(&response_writer_label)
            .map_err(|err| {
                warn!("could not create HTTP response channel: {:?}", err);
            })?;

        Ok(Pipe {
            request_writer,
            request_reader,
            response_writer,
            response_reader,
        })
    }

    fn insert_message(&self, runtime: &RuntimeProxy, request: HttpRequest) -> Result<(), ()> {
        // Put the HTTP request message inside the per-invocation request channel.
        let sender = crate::io::Sender::new(WriteHandle {
            handle: self.request_writer,
        });
        info!("@@@@@@@@ Sending request to Oak node");
        sender.send(request, runtime).map_err(|err| {
            error!(
                "Couldn't write the request to the HTTP request channel: {:?}",
                err
            )
        })
    }

    fn send_invocation(
        &self,
        runtime: &RuntimeProxy,
        invocation_channel: oak_abi::Handle,
    ) -> Result<(), ()> {
        // Create an invocation containing request-specific channels.
        let invocation = HttpInvocation {
            receiver: Some(Receiver::new(ReadHandle {
                handle: self.request_reader,
            })),
            sender: Some(Sender::new(WriteHandle {
                handle: self.response_writer,
            })),
        };
        let invocation_sender = crate::io::Sender::new(WriteHandle {
            handle: invocation_channel,
        });
        info!("@@@@@@@@ Sending invocation");
        invocation_sender
            .send(invocation, runtime)
            .map_err(|error| {
                error!("Couldn't write the invocation message: {:?}", error);
            })
    }

    // Close all local handles except for the one that allows reading responses.
    fn close(&self, runtime: &RuntimeProxy) {
        if let Err(err) = runtime.channel_close(self.request_writer) {
            error!(
                "Failed to close request writer channel for invocation: {:?}",
                err
            );
        }
        if let Err(err) = runtime.channel_close(self.request_reader) {
            error!(
                "Failed to close request reader channel for invocation: {:?}",
                err
            );
        }
        if let Err(err) = runtime.channel_close(self.response_writer) {
            error!(
                "Failed to close response writer channel for invocation: {:?}",
                err
            );
        }
    }
}
