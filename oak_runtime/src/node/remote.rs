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

//! Functionality for communication with a remote Runtime.

use crate::{
    node::{ConfigurationError, Node},
    proto::oak::remote::{
        encap::{
            ChannelWriteRequest, ChannelWriteResponse, NodeCreateRequest, NodeCreateResponse,
            RemoteHandle,
        },
        remote_runtime_client::RemoteRuntimeClient,
    },
    CreatedNode, NodePrivilege, RuntimeProxy,
};
use anyhow::Context;
use log::{error, info, warn};
use oak_abi::{label::Label, ChannelReadStatus, OakStatus};
use oak_io::{handle::ReadHandle, OakError};
use tokio::sync::oneshot;
use tonic::transport::Channel;

use crate::io::{Receiver, ReceiverExt};
use oak_abi::proto::oak::application::ExternalConnectionConfiguration;

/// ExternalConnection node that can serve as a stub for a remote Runtime.
pub struct ExternalConnectionNode {
    /// Pseudo-Node name.
    node_name: String,
    // Address of the remote Runtime
    remote_addr: String,
    // Address of the local Runtime
    local_addr: String,
}

impl ExternalConnectionNode {
    pub fn new(
        node_name: &str,
        config: &ExternalConnectionConfiguration,
    ) -> Result<Self, ConfigurationError> {
        Ok(ExternalConnectionNode {
            node_name: node_name.to_string(),
            remote_addr: config.remote_addr.clone(),
            local_addr: config.local_addr.clone(),
        })
    }
}

impl Node for ExternalConnectionNode {
    fn node_type(&self) -> &'static str {
        "external-connection"
    }

    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        startup_handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        let receiver = Receiver::<NodeCreateRequest>::new(ReadHandle {
            handle: startup_handle,
        });
        let mut async_runtime = create_async_runtime(runtime.clone());
        loop {
            match receiver.receive(&runtime) {
                Ok(req) => {
                    let initial_handle = req.initial_handle;
                    let label = req.label.clone().unwrap_or_else(Label::public_untrusted);
                    // Send the node_create request to the remote, and await response
                    let response = async_runtime
                        .block_on(send_node_create_request(&self.remote_addr, req))
                        .expect("Couldn't get response from the remote.")
                        .into_inner();

                    // Create a DummySender nodes for the receiver (init-handle) in the request.
                    let remote_write_half = *response
                        .handles_map
                        .get(&initial_handle)
                        .expect("Couldn't find remote_write_half in the handles_map");
                    let sender = DummySender {
                        remote_write_half,
                        remote_addr: self.remote_addr.clone(),
                        local_addr: self.local_addr.clone(),
                    };
                    // Register the DummySender node
                    let res = runtime.node_register(
                        CreatedNode {
                            instance: Box::new(sender),
                            privilege: NodePrivilege::default(),
                        },
                        "dummy-sender",
                        &label,
                        initial_handle,
                    );
                    if res.is_err() {
                        warn!("Couldn't register sender node");
                    }
                }
                // Recoverable errors:
                Err(OakError::ProtobufDecodeError(err)) => {
                    warn!(
                        "{} failed to decode remote node create request: {:?}",
                        self.node_name, err
                    );
                }
                // Errors that lead to Node termination:
                Err(OakError::OakStatus(OakStatus::ErrTerminated)) => break,
                Err(OakError::OakStatus(OakStatus::ErrChannelClosed)) => {
                    info!("{} channel closed", self.node_name);
                    break;
                }
                Err(err) => {
                    error!("{} failed channel receive: {:?}", self.node_name, err);
                    break;
                }
            }
        }
        info!("{} external connection complete", self.node_name);
        let _ = runtime.channel_close(startup_handle);
    }
}

/// A node that enables sending messages to a channel on a remote Runtime. Tries to read from its
/// read_half in a loop. Whenever there is a message available, this node sends a
/// `remote_channel_write` to the remote. The remote Runtime then writes the message on the
/// corresponding write handle.
/// TODO: Can this be merged with ExternalConnection node? We have wait_on_channels that waits on
/// multiple channels. Do we have channels_read too to read from multiple channels?
struct DummySender {
    // Remote handle, to be included in the messages sent to the remote.
    remote_write_half: oak_abi::Handle,
    // Address of the remote client
    remote_addr: String,
    // Address of this runtime
    local_addr: String,
}

impl Node for DummySender {
    fn node_type(&self) -> &'static str {
        "dummy-receiver"
    }

    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        // Async runtime for sending channel_write requests to the remote.
        let mut async_runtime = create_async_runtime(runtime.clone());

        // Wait for messages on the `handle`. Send `remote_channel_write` whenever there is a
        // message on `read_half`
        loop {
            let read_status = match runtime.wait_on_channels(&[handle]) {
                Ok(statuses) => statuses,
                Err(OakStatus::ErrTerminated) => {
                    info!("Terminating DummySender as the Runtime is terminated.");
                    break;
                }
                Err(err) => {
                    panic!("Should not have reached here: {}", err);
                }
            };

            match read_status[0] {
                ChannelReadStatus::ReadReady => {
                    let message = runtime.channel_read(handle).and_then(|message| {
                        message.ok_or_else(|| {
                            error!("Channel read error {:?}: Empty message", handle);
                            OakStatus::ErrInternal
                        })
                    });
                    match message {
                        // The message that is received on the input channel, will be send to
                        // the remote without any modification, apart from replacing the handle with
                        // RemoteHandles, with Runtime addresses.

                        // TODO: An additional lookup in a local map is needed to replace local
                        // handles that represent remote channels with URIs of the original handles.
                        Ok(msg) => {
                            let handles = msg
                                .handles
                                .into_iter()
                                .map(|handle| RemoteHandle {
                                    raw_handle: handle,
                                    runtime_addr: self.local_addr.clone(),
                                })
                                .collect();

                            let req = ChannelWriteRequest {
                                write_handle: self.remote_write_half,
                                data: msg.bytes,
                                handles,
                            };
                            // Send the node_create request to the remote, and await response
                            let response = async_runtime
                                .block_on(send_channel_write_request(&self.remote_addr, req))
                                .expect("Couldn't get response from the remote.")
                                .into_inner();
                            // TODO: Copy the handle map to internal handles_map
                            info!("Size of handles_map: {}", response.handles_map.len());
                        }
                        Err(err) => error!("Channel read error {:?}", err),
                    }
                }
                ChannelReadStatus::Orphaned => {
                    info!("Channel closed {:?}", handle);
                    // TODO: send remote_channel_close
                    break;
                }
                status => {
                    error!("Channel read error {:?}: {:?}", handle, status);
                    // Continue with the loop
                }
            }
        }
    }
}

fn create_async_runtime(runtime: RuntimeProxy) -> tokio::runtime::Runtime {
    tokio::runtime::Builder::new()
        // Use simple scheduler that runs all tasks on the current-thread.
        // https://docs.rs/tokio/0.2.16/tokio/runtime/index.html#basic-scheduler
        .basic_scheduler()
        // Enables the I/O driver.
        // Necessary for using net, process, signal, and I/O types on the Tokio runtime.
        .enable_io()
        // Enables the time driver.
        // Necessary for creating a Tokio Runtime.
        .enable_time()
        .on_thread_start(move || runtime.set_as_current())
        .build()
        .expect("Couldn't create Async runtime")
}

async fn send_node_create_request(
    remote_addr: &str,
    req: NodeCreateRequest,
) -> anyhow::Result<tonic::Response<NodeCreateResponse>> {
    let channel = Channel::from_shared(remote_addr.to_owned())?
        .connect()
        .await?;

    let mut client = RemoteRuntimeClient::new(channel);
    client
        .node_create(req)
        .await
        .context("failed to create node")
}

async fn send_channel_write_request(
    remote_addr: &str,
    req: ChannelWriteRequest,
) -> anyhow::Result<tonic::Response<ChannelWriteResponse>> {
    let channel = Channel::from_shared(remote_addr.to_owned())?
        .connect()
        .await?;

    let mut client = RemoteRuntimeClient::new(channel);
    client
        .channel_write(req)
        .await
        .context("failed to write into the channel")
}
