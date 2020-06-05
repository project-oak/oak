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

//! RuntimeProxy functionality, allowing manipulation of Nodes, channels and messages within the
//! context of a specific Node or pseudo-Node.

use crate::{
    message::NodeMessage,
    metrics::Metrics,
    runtime::{graph::DotGraph, AuxServer, NodeId, NodePrivilege, NodeReadStatus, Runtime},
    GrpcConfiguration,
};
use core::sync::atomic::{AtomicBool, AtomicU64};
use log::debug;
use oak_abi::{
    label::Label,
    proto::oak::application::{ApplicationConfiguration, NodeConfiguration},
    ChannelReadStatus, OakStatus,
};
use std::{
    collections::HashMap,
    string::String,
    sync::{Arc, Mutex, RwLock},
};

/// A proxy object that binds together a reference to the underlying [`Runtime`] with a single
/// [`NodeId`].
///
/// This can be considered as the interface to the [`Runtime`] that Node and pseudo-Node
/// implementations have access to.
///
/// Each [`RuntimeProxy`] instance is used by an individual Node or pseudo-Node instance to
/// communicate with the [`Runtime`]. Nodes do not have direct access to the [`Runtime`] apart from
/// through [`RuntimeProxy`], which exposes a more limited API, and ensures that Nodes cannot
/// impersonate each other.
///
/// Individual methods simply forward to corresponding methods on the underlying [`Runtime`], by
/// partially applying the first argument (the stored [`NodeId`]).
#[derive(Clone)]
pub struct RuntimeProxy {
    pub(super) runtime: Arc<Runtime>,
    pub node_id: NodeId,
}

// Methods on `RuntimeProxy` for managing the core `Runtime` instance.
impl RuntimeProxy {
    /// Creates a [`Runtime`] instance with a single initial Node configured, and no channels.
    pub fn create_runtime(
        application_configuration: ApplicationConfiguration,
        grpc_configuration: GrpcConfiguration,
    ) -> RuntimeProxy {
        let runtime = Arc::new(Runtime {
            application_configuration,
            grpc_configuration,
            terminating: AtomicBool::new(false),
            next_channel_id: AtomicU64::new(0),

            node_infos: RwLock::new(HashMap::new()),

            next_node_id: AtomicU64::new(0),

            aux_servers: Mutex::new(Vec::new()),

            metrics_data: Metrics::new(),
        });
        let proxy = runtime.proxy_for_new_node();
        proxy.runtime.node_configure_instance(
            proxy.node_id,
            "implicit.initial",
            &Label::public_untrusted(),
            &NodePrivilege::default(),
        );
        proxy
    }

    /// Configures and runs the protobuf specified [`ApplicationConfiguration`].
    ///
    /// After starting a [`Runtime`], calling [`Runtime::stop`] will notify all Nodes that they
    /// should terminate, and wait for them to terminate.
    ///
    /// Returns a writable [`oak_abi::Handle`] to send messages into the initial Node created from
    /// the configuration.
    pub fn start_runtime(
        &self,
        runtime_configuration: crate::RuntimeConfiguration,
    ) -> Result<oak_abi::Handle, OakStatus> {
        let node_configuration = self
            .runtime
            .application_configuration
            .initial_node_configuration
            .as_ref()
            .ok_or(OakStatus::ErrInvalidArgs)?;

        self.metrics_data()
            .runtime_metrics
            .runtime_health_check
            .set(1);

        if cfg!(feature = "oak_debug") {
            if let Some(port) = runtime_configuration.introspect_port {
                self.runtime
                    .aux_servers
                    .lock()
                    .unwrap()
                    .push(AuxServer::new(
                        "introspect",
                        port,
                        self.runtime.clone(),
                        crate::runtime::introspect::serve,
                    ));
            }
        }
        if let Some(port) = runtime_configuration.metrics_port {
            self.runtime
                .aux_servers
                .lock()
                .unwrap()
                .push(AuxServer::new(
                    "metrics",
                    port,
                    self.runtime.clone(),
                    crate::metrics::server::start_metrics_server,
                ));
        }

        // When first starting, we assign the least privileged label to the channel connecting the
        // outside world to the entry point Node.
        let (write_handle, read_handle) = self.channel_create(&Label::public_untrusted())?;
        debug!(
            "{:?}: created initial channel ({}, {})",
            self.node_id, write_handle, read_handle,
        );

        self.node_create(
            &node_configuration,
            // When first starting, we assign the least privileged label to the entry point Node.
            &Label::public_untrusted(),
            read_handle,
        )?;
        self.channel_close(read_handle)
            .expect("could not close channel");

        Ok(write_handle)
    }

    /// Generate a Graphviz dot graph that shows the current shape of the Nodes and Channels in
    /// the runtime.
    #[cfg(feature = "oak_debug")]
    pub fn graph_runtime(&self) -> String {
        self.runtime.graph()
    }

    /// Signal termination to a [`Runtime`] and wait for its Node threads to terminate.
    pub fn stop_runtime(&self) {
        self.runtime.stop()
    }

    /// Create a RuntimeProxy instance that acts as a proxy for the specified NodeId.
    pub fn new_for_node(&self, node_id: NodeId) -> Self {
        RuntimeProxy {
            runtime: self.runtime.clone(),
            node_id,
        }
    }
    /// See [`Runtime::is_terminating`].
    pub fn is_terminating(&self) -> bool {
        self.runtime.is_terminating()
    }

    /// See [`Runtime::node_create`].
    pub fn node_create(
        &self,
        config: &NodeConfiguration,
        label: &Label,
        initial_handle: oak_abi::Handle,
    ) -> Result<(), OakStatus> {
        self.runtime
            .clone()
            .node_create(self.node_id, config, label, initial_handle)
    }

    /// See [`Runtime::channel_create`].
    pub fn channel_create(
        &self,
        label: &Label,
    ) -> Result<(oak_abi::Handle, oak_abi::Handle), OakStatus> {
        self.runtime.channel_create(self.node_id, label)
    }

    /// See [`Runtime::channel_close`].
    pub fn channel_close(&self, handle: oak_abi::Handle) -> Result<(), OakStatus> {
        self.runtime.channel_close(self.node_id, handle)
    }

    /// See [`Runtime::wait_on_channels`].
    pub fn wait_on_channels(
        &self,
        read_handles: &[oak_abi::Handle],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
        self.runtime.wait_on_channels(self.node_id, read_handles)
    }

    /// See [`Runtime::channel_write`].
    pub fn channel_write(
        &self,
        write_handle: oak_abi::Handle,
        msg: NodeMessage,
    ) -> Result<(), OakStatus> {
        self.runtime.channel_write(self.node_id, write_handle, msg)
    }

    /// See [`Runtime::channel_read`].
    pub fn channel_read(
        &self,
        read_handle: oak_abi::Handle,
    ) -> Result<Option<NodeMessage>, OakStatus> {
        self.runtime.channel_read(self.node_id, read_handle)
    }

    /// See [`Runtime::channel_try_read_message`].
    pub fn channel_try_read_message(
        &self,
        read_handle: oak_abi::Handle,
        bytes_capacity: usize,
        handles_capacity: usize,
    ) -> Result<Option<NodeReadStatus>, OakStatus> {
        self.runtime.channel_try_read_message(
            self.node_id,
            read_handle,
            bytes_capacity,
            handles_capacity,
        )
    }

    pub fn metrics_data(&self) -> Metrics {
        self.runtime.metrics_data.clone()
    }
}
