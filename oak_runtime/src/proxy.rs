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
    metrics::Metrics, AuxServer, ChannelHalfDirection, LabelReadStatus, NodeId, NodeMessage,
    NodePrivilege, NodeReadStatus, Runtime, SecureServerConfiguration, SignatureTable,
};
use core::sync::atomic::{AtomicBool, AtomicU64};
use log::debug;
use oak_abi::{
    label::Label,
    proto::oak::application::{ApplicationConfiguration, NodeConfiguration},
    ChannelReadStatus, OakStatus,
};
use std::{
    collections::{HashMap, VecDeque},
    sync::{Arc, Mutex, RwLock},
};

#[cfg(test)]
use crate::node::Node;

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
    pub runtime: Arc<Runtime>,
    pub node_id: NodeId,
    // The node_name is stored as a on-off copy for debug calls.
    // TODO(#1737): Move debug calls to the Runtime.
    pub node_name: String,
}

// Methods on `RuntimeProxy` for managing the core `Runtime` instance.
impl RuntimeProxy {
    /// Creates a [`Runtime`] instance with a single initial Node configured, and no channels.
    pub fn create_runtime(
        application_configuration: &ApplicationConfiguration,
        secure_server_configuration: &SecureServerConfiguration,
        signature_table: &SignatureTable,
    ) -> RuntimeProxy {
        let runtime = Arc::new(Runtime {
            terminating: AtomicBool::new(false),
            next_channel_id: AtomicU64::new(0),
            node_infos: RwLock::new(HashMap::new()),
            next_node_id: AtomicU64::new(0),
            aux_servers: Mutex::new(Vec::new()),
            introspection_event_queue: Mutex::new(VecDeque::new()),
            metrics_data: Metrics::new(),
            node_factory: crate::node::ServerNodeFactory {
                application_configuration: application_configuration.clone(),
                secure_server_configuration: secure_server_configuration.clone(),
                signature_table: signature_table.clone(),
            },
        });
        let proxy = runtime.proxy_for_new_node("implicit.initial");
        let new_node_id = proxy.node_id;
        let new_node_name = proxy.node_name.clone();
        proxy.runtime.node_configure_instance(
            new_node_id,
            "implicit",
            new_node_name,
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
            .node_factory
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
                        crate::introspect::serve,
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
        // outside world to the entrypoint Node.
        let (write_handle, read_handle) =
            self.channel_create("Initial", &Label::public_untrusted())?;
        debug!(
            "{:?}: created initial channel ({}, {})",
            self.node_name, write_handle, read_handle,
        );

        self.node_create(
            "Initial",
            &node_configuration,
            // When first starting, we assign the least privileged label to the entrypoint Node.
            &Label::public_untrusted(),
            read_handle,
        )?;
        self.channel_close(read_handle)
            .expect("could not close channel");

        Ok(write_handle)
    }

    /// See [`Runtime::is_terminating`].
    pub fn is_terminating(&self) -> bool {
        self.runtime.is_terminating()
    }

    /// See [`Runtime::node_create_and_register`].
    pub fn node_create(
        &self,
        name: &str,
        config: &NodeConfiguration,
        label: &Label,
        initial_handle: oak_abi::Handle,
    ) -> Result<(), OakStatus> {
        debug!(
            "{:?}: node_create({:?}, {:?}, {:?})",
            self.node_name, name, config, label
        );
        let result = self.runtime.clone().node_create_and_register(
            self.node_id,
            name,
            config,
            label,
            initial_handle,
        );
        debug!(
            "{:?}: node_create({:?}, {:?}, {:?}) -> {:?}",
            self.node_name, name, config, label, result
        );
        result
    }

    /// See [`Runtime::node_register`]. This is exposed to facilitate testing.
    #[cfg(test)]
    pub fn node_register(
        &self,
        instance: Box<dyn Node>,
        node_name: &str,
        label: &Label,
        initial_handle: oak_abi::Handle,
    ) -> Result<(), OakStatus> {
        debug!(
            "{:?}: register_node_instance(node_name: {:?}, label: {:?})",
            self.node_name, node_name, label
        );
        let result = self.runtime.clone().node_register(
            self.node_id,
            instance,
            node_name,
            label,
            initial_handle,
        );
        debug!(
            "{:?}: register_node_instance(node_name: {:?}, label: {:?}) -> {:?}",
            self.node_name, node_name, label, result
        );
        result
    }

    /// See [`Runtime::channel_create`].
    pub fn channel_create(
        &self,
        name: &str,
        label: &Label,
    ) -> Result<(oak_abi::Handle, oak_abi::Handle), OakStatus> {
        debug!(
            "{:?}: channel_create({:?}, {:?})",
            self.node_name, name, label
        );
        let result = self.runtime.channel_create(self.node_id, name, label);
        debug!(
            "{:?}: channel_create({:?}, {:?}) -> {:?}",
            self.node_name, name, label, result
        );
        result
    }

    /// See [`Runtime::channel_close`].
    pub fn channel_close(&self, handle: oak_abi::Handle) -> Result<(), OakStatus> {
        debug!("{:?}: channel_close({})", self.node_name, handle);
        let result = self.runtime.channel_close(self.node_id, handle);
        debug!(
            "{:?}: channel_close({}) -> {:?}",
            self.node_name, handle, result
        );
        result
    }

    /// See [`Runtime::wait_on_channels`].
    pub fn wait_on_channels(
        &self,
        read_handles: &[oak_abi::Handle],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
        debug!(
            "{:?}: wait_on_channels(count={})",
            self.node_name,
            read_handles.len()
        );
        let result = self.runtime.wait_on_channels(self.node_id, read_handles);
        debug!(
            "{:?}: wait_on_channels(count={}) -> {:?}",
            self.node_name,
            read_handles.len(),
            result
        );
        result
    }

    /// See [`Runtime::channel_write`].
    pub fn channel_write(
        &self,
        write_handle: oak_abi::Handle,
        msg: NodeMessage,
    ) -> Result<(), OakStatus> {
        debug!(
            "{:?}: channel_write({}, {:?})",
            self.node_name, write_handle, msg
        );
        let result = self.runtime.channel_write(self.node_id, write_handle, msg);
        debug!(
            "{:?}: channel_write({}, ...) -> {:?}",
            self.node_name, write_handle, result
        );
        result
    }

    /// See [`Runtime::channel_read`].
    pub fn channel_read(
        &self,
        read_handle: oak_abi::Handle,
    ) -> Result<Option<NodeMessage>, OakStatus> {
        debug!("{:?}: channel_read({})", self.node_name, read_handle,);
        let result = self.runtime.channel_read(self.node_id, read_handle);
        debug!(
            "{:?}: channel_read({}) -> {:?}",
            self.node_name, read_handle, result
        );
        result
    }

    /// See [`Runtime::channel_try_read_message`].
    pub fn channel_try_read_message(
        &self,
        read_handle: oak_abi::Handle,
        bytes_capacity: usize,
        handles_capacity: usize,
    ) -> Result<Option<NodeReadStatus>, OakStatus> {
        debug!(
            "{:?}: channel_try_read({}, bytes_capacity={}, handles_capacity={})",
            self.node_name, read_handle, bytes_capacity, handles_capacity
        );
        let result = self.runtime.channel_try_read_message(
            self.node_id,
            read_handle,
            bytes_capacity,
            handles_capacity,
        );
        debug!(
            "{:?}: channel_try_read({}, bytes_capacity={}, handles_capacity={}) -> {:?}",
            self.node_name, read_handle, bytes_capacity, handles_capacity, result
        );
        result
    }

    /// See [`Runtime::get_serialized_channel_label`].
    pub fn get_serialized_channel_label(
        &self,
        handle: oak_abi::Handle,
        capacity: usize,
    ) -> Result<LabelReadStatus, OakStatus> {
        debug!(
            "{:?}: get_serialized_channel_label({}, capacity={})",
            self.node_name, handle, capacity
        );
        let result = self
            .runtime
            .get_serialized_channel_label(self.node_id, handle, capacity);
        debug!(
            "{:?}: get_serialized_channel_label({}, capacity={}) -> {:?}",
            self.node_name, handle, capacity, result
        );
        result
    }

    /// See [`Runtime::get_serialized_node_label`].
    pub fn get_serialized_node_label(&self, capacity: usize) -> Result<LabelReadStatus, OakStatus> {
        debug!(
            "{:?}: get_serialized_node_label(capacity={})",
            self.node_name, capacity
        );
        let result = self
            .runtime
            .get_serialized_node_label(self.node_id, capacity);
        debug!(
            "{:?}: get_serialized_node_label(capacity={}) -> {:?}",
            self.node_name, capacity, result
        );
        result
    }

    /// See [`Runtime::get_serialized_node_privilege`].
    pub fn get_serialized_node_privilege(
        &self,
        capacity: usize,
    ) -> Result<LabelReadStatus, OakStatus> {
        debug!(
            "{:?}: get_serialized_node_privilege(capacity={})",
            self.node_name, capacity
        );
        let result = self
            .runtime
            .get_serialized_node_privilege(self.node_id, capacity);
        debug!(
            "{:?}: get_serialized_node_privilege(capacity={}) -> {:?}",
            self.node_name, capacity, result
        );
        result
    }

    /// See [`Runtime::get_channel_label`].
    pub fn get_channel_label(&self, handle: oak_abi::Handle) -> Result<Label, OakStatus> {
        debug!("{:?}: get_channel_label({})", self.node_name, handle);
        let result = self.runtime.get_channel_label(self.node_id, handle);
        debug!(
            "{:?}: get_channel_label({}) -> {:?}",
            self.node_name, handle, result
        );
        result
    }

    /// Return the direction of an ABI handle.
    pub fn channel_direction(
        &self,
        handle: oak_abi::Handle,
    ) -> Result<ChannelHalfDirection, OakStatus> {
        self.runtime.abi_direction(self.node_id, handle)
    }

    pub fn metrics_data(&self) -> Metrics {
        self.runtime.metrics_data.clone()
    }
}
