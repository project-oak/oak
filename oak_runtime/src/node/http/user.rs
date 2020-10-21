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

//! A `UserNode` is a virtual node that is created per user request and serves as a router between
//! an HTTP server pseudo-Node and an Oak node that serves the incoming HTTP requests. The
//! `UserNode` forwards the requests to the Oak node, and returns the responses back to the HTTP
//! server pseudo-Node. We set the user's identity (extracted from the incoming request) as both the
//! declassification and endorsement privileges of the `UserNode`. This allows the `UserNode` to
//! assign user-specific labels to the communication channels with the Oak node. The HTTP server
//! pseudo-Node cannot create channels with such user-specific labels itself. User-specific labels
//! are required to prevent any potential leakage by the Oak node.

use crate::{
    io::{Receiver, ReceiverExt, Sender, SenderExt},
    node::{ConfigurationError, Node, NodePrivilege},
    proto::oak::invocation::{HttpInvocation, OuterHttpInvocation},
    RuntimeProxy,
};
use log::{error, trace, warn};
use oak_abi::{
    label::{Label, Tag, UserIdentityTag},
    proto::oak::application::UserNodeConfiguration,
};
use oak_io::handle::{ReadHandle, WriteHandle};
use oak_services::proto::oak::encap::HttpRequest;
use std::collections::HashSet;
use tokio::sync::oneshot;

/// Struct that represents a user node, with its privilege set to the user's identity as both the
/// declassification and the endorsement tags.
pub struct UserNode {
    /// Pseudo-Node name.
    node_name: String,
    /// The privilege of the node.
    privilege: NodePrivilege,
}

impl UserNode {
    pub fn new(node_name: &str, config: UserNodeConfiguration) -> Result<Self, ConfigurationError> {
        let mut privilege_tags = HashSet::new();
        privilege_tags.insert(Tag {
            tag: Some(oak_abi::label::tag::Tag::UserIdentityTag(UserIdentityTag {
                public_key: config.privilege,
            })),
        });

        let privilege = NodePrivilege {
            can_declassify_confidentiality_tags: privilege_tags.clone(),
            can_endorse_integrity_tags: privilege_tags,
        };
        Ok(UserNode {
            node_name: node_name.to_string(),
            privilege,
        })
    }

    /// Creates a `request` and a `response` channel for communication with the Oak node. Uses the
    /// `request` channel to send the HTTP request to the Oak node, and returns a handle to the
    /// response channel for receiving the response from the Oak node.
    fn inject_http_request(
        &self,
        runtime: RuntimeProxy,
        outer_http_invocation: OuterHttpInvocation,
    ) -> Result<oak_abi::Handle, ()> {
        // Create a pair of temporary channels to pass the HTTP request to the Oak node, and to
        // receive the response from it.
        let pipe = Pipe::new(
            &runtime,
            &outer_http_invocation
                .request_label
                .ok_or(())
                .map_err(|_err| {
                    warn!("Cannot retrieve request_label from the OuterHttpInvocation");
                })?,
            &self.privilege,
        )?;

        // Put the HTTP request message inside the per-invocation request channel.
        pipe.insert_message(
            &runtime,
            outer_http_invocation.request.ok_or(()).map_err(|_err| {
                warn!("Cannot retrieve request from the OuterHttpInvocation");
            })?,
        )?;

        // Send an invocation message (with attached handles) to the Oak Node.
        trace!(
            "UserNode {:?}: Sending invocation on outer_http_invocation.invocation_sender",
            self.node_name
        );
        pipe.send_invocation(
            &runtime,
            outer_http_invocation
                .invocation_sender
                .ok_or(())
                .map_err(|_err| {
                    warn!("Cannot retrieve invocation_sender from the OuterHttpInvocation");
                })?
                .handle
                .handle,
        )?;

        // Close all local handles except for the one that allows reading responses.
        pipe.close(&runtime);

        Ok(pipe.response_reader)
    }

    fn try_run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        startup_handle: oak_abi::Handle,
    ) -> Result<(), ()> {
        let receiver = Receiver::<OuterHttpInvocation>::new(ReadHandle {
            handle: startup_handle,
        });
        let outer_http_invocation = receiver.receive(&runtime).map_err(|err| {
            error!(
                "{}: Failed to retrieve the outer HTTP invocation: {:?}",
                self.node_name, err
            )
        })?;

        // Send the request to the Oak node and get a handle to the channel containing the response.
        let response_reader =
            self.inject_http_request(runtime.clone(), outer_http_invocation.clone())?;
        let response_receiver = crate::io::Receiver::new(ReadHandle {
            handle: response_reader,
        });
        let response = response_receiver.receive(&runtime).map_err(|err| {
            error!(
                "Could not receive the response from the Oak node on channel {}: {}.",
                response_reader, err
            )
        })?;

        outer_http_invocation
            .response_sender
            .ok_or(())
            .and_then(|sender| {
                sender.send(response, &runtime).map_err(|err| {
                    warn!(
                        "{}: Could not send response to HTTP server pseudo-node: {}",
                        self.node_name, err,
                    )
                })
            })
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
        let _unit_result = self.try_run(runtime, startup_handle);
    }

    fn get_privilege(&self) -> NodePrivilege {
        self.privilege.clone()
    }
}

/// A pair of temporary channels to pass the HTTP request to the Oak node, and to receive the
/// response.
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
        let request_reader_label = Label {
            confidentiality_tags: request_label.confidentiality_tags.clone(),
            integrity_tags: privilege
                .can_endorse_integrity_tags
                .clone()
                .into_iter()
                .collect(),
        };
        let response_writer_label = Label {
            confidentiality_tags: privilege
                .can_declassify_confidentiality_tags
                .clone()
                .into_iter()
                .collect(),
            integrity_tags: vec![],
        };

        // Create a channel for passing HTTP requests to the Oak node. This channel is created with
        // the label specified by the caller, and the identity of the caller.
        let (request_writer, request_reader) = runtime
            .channel_create(&request_reader_label)
            .map_err(|err| {
                warn!("could not create HTTP request channel: {:?}", err);
            })?;

        // Create a channel for receiving HTTP responses from the Oak node. This channel is created
        // with a label that has the identity of the caller as the confidentiality component.
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

    /// Puts the HttpRequest in the `request_sender` channel, ready to be read by the Oak node.
    fn insert_message(&self, runtime: &RuntimeProxy, request: HttpRequest) -> Result<(), ()> {
        // Put the HTTP request message inside the per-invocation request channel.
        let sender = crate::io::Sender::new(WriteHandle {
            handle: self.request_writer,
        });
        sender.send(request, runtime).map_err(|err| {
            error!(
                "Couldn't write the request to the HTTP request channel: {:?}",
                err
            )
        })
    }

    /// Sends an instance of [`HttpInvocation`] to the Oak node. The [`HttpInvocation`] instance
    /// contains two request-specific channels, one that allows the Oak node to read the request,
    /// and one on which the Oak node sends the response.
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
