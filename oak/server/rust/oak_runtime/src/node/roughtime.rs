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

//! Roughtime client pseudo-Node functionality.

use crate::{
    io::Receiver,
    node::grpc::invocation::Invocation,
    runtime::RuntimeProxy,
    time::{
        get_default_servers, RoughtimeClient, RoughtimeServer, DEFAULT_MAX_RADIUS_MICROSECONDS,
        DEFAULT_MIN_OVERLAPPING_INTERVALS, DEFAULT_SERVER_RETRIES, DEFAULT_TIMEOUT_SECONDS,
    },
};
use log::{debug, error, info};
use oak_abi::{
    proto::{
        google::rpc::Code,
        oak::{
            application::RoughtimeClientConfiguration,
            encap::GrpcResponse,
            roughtime::{RoughtimeRequest, RoughtimeResponse},
        },
    },
    OakStatus,
};
use prost::Message;
use tokio::sync::oneshot;

/// Roughtime client pseudo-Node.
pub struct RoughtimeClientNode {
    node_name: String,
    client: RoughtimeClient,
}

impl RoughtimeClientNode {
    /// Creates a new [`RoughtimeClientNode`] instance, but does not start it.
    pub fn new(node_name: &str, config: &RoughtimeClientConfiguration) -> Self {
        let timeout_seconds = if config.timeout_seconds == 0 {
            DEFAULT_TIMEOUT_SECONDS
        } else {
            config.timeout_seconds as u64
        };
        let server_retries = if config.server_retries == 0 {
            DEFAULT_SERVER_RETRIES
        } else {
            config.server_retries as usize
        };
        let min_overlapping_intervals = if config.min_overlapping_intervals == 0 {
            DEFAULT_MIN_OVERLAPPING_INTERVALS
        } else {
            config.min_overlapping_intervals as usize
        };
        let max_radius_microseconds = if config.max_radius_microseconds == 0 {
            DEFAULT_MAX_RADIUS_MICROSECONDS
        } else {
            config.max_radius_microseconds
        };
        let servers = if config.servers.is_empty() {
            get_default_servers()
        } else {
            config
                .servers
                .iter()
                .map(|server| {
                    RoughtimeServer::new(
                        &server.name,
                        &server.host,
                        server.port as u16,
                        &server.public_key_base64,
                    )
                })
                .collect()
        };

        Self {
            node_name: node_name.to_string(),
            client: RoughtimeClient::new(
                servers,
                min_overlapping_intervals,
                max_radius_microseconds,
                timeout_seconds,
                server_retries,
            ),
        }
    }

    /// Processes a gRPC invocation.
    fn process_invocation(&self, runtime: &RuntimeProxy, invocation: &Invocation) {
        match invocation.receive_request(runtime) {
            Ok(request) => {
                if request.method_name != "/oak.roughtime.RoughtimeService/GetRoughtime" {
                    let message = format!("Unknown method_name: {}", request.method_name);
                    invocation.send_error(Code::NotFound, &message, runtime);
                }
                if RoughtimeRequest::decode(request.req_msg.as_slice()).is_err() {
                    invocation.send_error(
                        Code::InvalidArgument,
                        "Could not parse request.",
                        runtime,
                    );
                }
            }
            Err(error) => {
                let message = format!("Error reading request: {:?}", error);
                invocation.send_error(Code::InvalidArgument, &message, runtime);
            }
        };

        match self.client.get_roughtime() {
            Ok(time) => {
                let response = RoughtimeResponse {
                    roughtime_usec: time,
                };
                let mut message = Vec::new();
                match response.encode(&mut message) {
                    Ok(_) => {
                        let grpc_response = GrpcResponse {
                            rsp_msg: message,
                            status: None,
                            last: true,
                        };
                        let _ = invocation
                            .send_response(grpc_response, runtime)
                            .map_err(|error| {
                                error!("Couldn't send the response: {:?}", error);
                            });
                    }
                    Err(error) => {
                        let message = format!("Error encoding response: {:?}", error);
                        invocation.send_error(Code::Internal, &message, runtime);
                    }
                }
            }
            Err(error) => {
                let message = format!("Error getting Roughtime: {:?}", error);
                invocation.send_error(Code::Internal, &message, runtime);
            }
        };
    }
}

impl super::Node for RoughtimeClientNode {
    /// Runs the node.
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        info!("{}: Starting Roughtime pseudo-Node", self.node_name);
        // Create a [`Receiver`] used for reading gRPC invocations.
        let receiver = Receiver::<Invocation>::new(handle);
        loop {
            debug!("Waiting for gRPC invocation");
            // Read a gRPC invocation from the [`Receiver`].
            match receiver.receive(&runtime) {
                Ok(invocation) => {
                    self.process_invocation(&runtime, &invocation);
                    invocation.close(&runtime);
                }
                Err(OakStatus::ErrTerminated) => {
                    break;
                }
                Err(error) => {
                    error!("Couldn't receive the invocation: {:?}", error);
                    break;
                }
            }
        }
    }
}
