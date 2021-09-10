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
    construct_debug_id, metrics::Metrics, node::ServerNodeFactory,
    permissions::PermissionsConfiguration, AuxServer, ChannelHalfDirection, Downgrading,
    LabelReadStatus, NodeId, NodeMessage, NodePrivilege, NodeReadStatus, Runtime,
    RuntimeConfiguration, SecureServerConfiguration, SignatureTable,
};
use core::sync::atomic::{AtomicBool, AtomicU64};
use log::debug;
use oak_abi::{
    label::Label,
    proto::oak::application::{ApplicationConfiguration, NodeConfiguration},
    ChannelReadStatus, OakStatus,
};
use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque},
    sync::{Arc, Mutex, RwLock},
};

#[cfg(test)]
use crate::node::CreatedNode;

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
    // The node_name is stored as a one-off copy for debug calls.
    // TODO(#1737): Move debug calls to the Runtime.
    pub node_name: String,
}

// Methods on `RuntimeProxy` for managing the core `Runtime` instance.
impl RuntimeProxy {
    /// Creates a [`Runtime`] instance with a single initial Node configured, and no channels.
    pub fn create_runtime(
        application_configuration: &ApplicationConfiguration,
        permissions_configuration: &PermissionsConfiguration,
        secure_server_configuration: &SecureServerConfiguration,
        signature_table: &SignatureTable,
        kms_credentials: Option<&std::path::PathBuf>,
    ) -> RuntimeProxy {
        let runtime = Arc::new(Runtime {
            terminating: AtomicBool::new(false),
            next_channel_id: AtomicU64::new(0),
            node_infos: RwLock::new(HashMap::new()),
            next_node_id: AtomicU64::new(0),
            aux_servers: Mutex::new(Vec::new()),
            introspection_event_queue: Mutex::new(VecDeque::new()),
            metrics_data: Metrics::new(),
            node_factory: ServerNodeFactory {
                application_configuration: application_configuration.clone(),
                permissions_configuration: permissions_configuration.clone(),
                secure_server_configuration: secure_server_configuration.clone(),
                signature_table: signature_table.clone(),
                kms_credentials: kms_credentials.map(|p| p.to_path_buf()),
            },
        });
        let new_node_name = "implicit.initial";
        let proxy = runtime.proxy_for_new_node(new_node_name);
        let new_node_id = proxy.node_id;
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
        runtime_configuration: RuntimeConfiguration,
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

        #[cfg(feature = "oak-unsafe")]
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
            self.get_debug_id(),
            write_handle,
            read_handle,
        );

        self.node_create(
            "Initial",
            node_configuration,
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

    /// Calls [`Runtime::node_create_and_register`] without using the Node's privilege.
    pub fn node_create(
        &self,
        name: &str,
        config: &NodeConfiguration,
        label: &Label,
        initial_handle: oak_abi::Handle,
    ) -> Result<(), OakStatus> {
        debug!(
            "{:?}: node_create({:?}, {:?}, {:?})",
            self.get_debug_id(),
            name,
            config,
            label
        );
        let result = self.runtime.clone().node_create_and_register(
            self.node_id,
            name,
            config,
            label,
            initial_handle,
            Downgrading::No,
        );
        debug!(
            "{:?}: node_create({:?}, {:?}, {:?}) -> {:?}",
            self.get_debug_id(),
            name,
            config,
            label,
            result
        );
        result
    }

    /// Calls [`Runtime::node_create_and_register`] using the Node's privilege.
    pub fn node_create_with_downgrade(
        &self,
        name: &str,
        config: &NodeConfiguration,
        label: &Label,
        initial_handle: oak_abi::Handle,
    ) -> Result<(), OakStatus> {
        debug!(
            "{:?}: node_create_with_downgrade({:?}, {:?}, {:?})",
            self.node_id, name, config, label
        );
        let result = self.runtime.clone().node_create_and_register(
            self.node_id,
            name,
            config,
            label,
            initial_handle,
            Downgrading::Yes,
        );
        debug!(
            "{:?}: node_create_with_downgrade({:?}, {:?}, {:?}) -> {:?}",
            self.node_id, name, config, label, result
        );
        result
    }

    /// See [`Runtime::node_register`]. This is exposed to facilitate testing.
    #[cfg(test)]
    pub fn node_register(
        &self,
        created_node: CreatedNode,
        node_name: &str,
        label: &Label,
        initial_handle: oak_abi::Handle,
    ) -> Result<(), OakStatus> {
        debug!(
            "{:?}: register_node_instance(node_name: {:?}, label: {:?})",
            self.get_debug_id(),
            node_name,
            label
        );
        let result = self.runtime.clone().node_register(
            self.node_id,
            created_node,
            node_name,
            label,
            initial_handle,
            Downgrading::No,
        );
        debug!(
            "{:?}: register_node_instance(node_name: {:?}, label: {:?}) -> {:?}",
            self.get_debug_id(),
            node_name,
            label,
            result
        );
        result
    }

    /// Calls [`Runtime::channel_create`] without using the Node's privilege.
    pub fn channel_create(
        &self,
        name: &str,
        label: &Label,
    ) -> Result<(oak_abi::Handle, oak_abi::Handle), OakStatus> {
        debug!(
            "{:?}: channel_create({:?}, {:?})",
            self.get_debug_id(),
            name,
            label
        );
        let result = self
            .runtime
            .channel_create(self.node_id, name, label, Downgrading::No);
        debug!(
            "{:?}: channel_create({:?}, {:?}) -> {:?}",
            self.get_debug_id(),
            name,
            label,
            result
        );
        result
    }

    /// Calls [`Runtime::channel_create`] using the Node's privilege.
    pub fn channel_create_with_downgrade(
        &self,
        name: &str,
        label: &Label,
    ) -> Result<(oak_abi::Handle, oak_abi::Handle), OakStatus> {
        debug!(
            "{:?}: channel_create_with_downgrade({:?}, {:?})",
            self.node_id, name, label
        );
        let result = self
            .runtime
            .channel_create(self.node_id, name, label, Downgrading::Yes);
        debug!(
            "{:?}: channel_create_with_downgrade({:?}, {:?}) -> {:?}",
            self.node_id, name, label, result
        );
        result
    }

    /// Calls [`Runtime::handle_clone`].
    pub fn handle_clone(&self, handle: oak_abi::Handle) -> Result<oak_abi::Handle, OakStatus> {
        debug!("{:?}: handle_clone({:?}", self.node_id, handle,);
        let result = self.runtime.handle_clone(self.node_id, handle);
        debug!(
            "{:?}: handle_clone({:?}) -> {:?}",
            self.node_id, handle, result
        );
        result
    }

    /// See [`Runtime::channel_close`].
    pub fn channel_close(&self, handle: oak_abi::Handle) -> Result<(), OakStatus> {
        debug!("{:?}: channel_close({})", self.get_debug_id(), handle);
        let result = self.runtime.channel_close(self.node_id, handle);
        debug!(
            "{:?}: channel_close({}) -> {:?}",
            self.get_debug_id(),
            handle,
            result
        );
        result
    }

    /// Calls [`Runtime::wait_on_channels`] without using the Node's privilege.
    pub fn wait_on_channels(
        &self,
        read_handles: &[oak_abi::Handle],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
        debug!(
            "{:?}: wait_on_channels(count={})",
            self.get_debug_id(),
            read_handles.len()
        );
        let result = self
            .runtime
            .wait_on_channels(self.node_id, read_handles, Downgrading::No);
        debug!(
            "{:?}: wait_on_channels(count={}) -> {:?}",
            self.get_debug_id(),
            read_handles.len(),
            result
        );
        result
    }

    /// Calls [`Runtime::wait_on_channels`] using the Node's privilege.
    pub fn wait_on_channels_with_downgrade(
        &self,
        read_handles: &[oak_abi::Handle],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
        debug!(
            "{:?}: wait_on_channels_with_downgrade(count={})",
            self.get_debug_id(),
            read_handles.len()
        );
        let result = self
            .runtime
            .wait_on_channels(self.node_id, read_handles, Downgrading::Yes);
        debug!(
            "{:?}: wait_on_channels_with_downgrade(count={}) -> {:?}",
            self.get_debug_id(),
            read_handles.len(),
            result
        );
        result
    }

    /// Calls [`Runtime::channel_write`] without using the Node's privilege.
    pub fn channel_write(
        &self,
        write_handle: oak_abi::Handle,
        msg: NodeMessage,
    ) -> Result<(), OakStatus> {
        debug!(
            "{:?}: channel_write({}, {:?})",
            self.get_debug_id(),
            write_handle,
            msg
        );
        let result = self
            .runtime
            .channel_write(self.node_id, write_handle, msg, Downgrading::No);
        debug!(
            "{:?}: channel_write({}, ...) -> {:?}",
            self.get_debug_id(),
            write_handle,
            result
        );
        result
    }

    /// Calls [`Runtime::channel_write`] using the Node's privilege.
    pub fn channel_write_with_downgrade(
        &self,
        write_handle: oak_abi::Handle,
        msg: NodeMessage,
    ) -> Result<(), OakStatus> {
        debug!(
            "{:?}: channel_write_with_downgrade({}, {:?})",
            self.node_id, write_handle, msg
        );
        let result = self
            .runtime
            .channel_write(self.node_id, write_handle, msg, Downgrading::Yes);
        debug!(
            "{:?}: channel_write_with_downgrade({}, ...) -> {:?}",
            self.node_id, write_handle, result
        );
        result
    }

    /// Calls [`Runtime::channel_read`] without using the Node's privilege.
    pub fn channel_read(
        &self,
        read_handle: oak_abi::Handle,
    ) -> Result<Option<NodeMessage>, OakStatus> {
        debug!("{:?}: channel_read({})", self.get_debug_id(), read_handle,);
        let result = self
            .runtime
            .channel_read(self.node_id, read_handle, Downgrading::No);
        debug!(
            "{:?}: channel_read({}) -> {:?}",
            self.get_debug_id(),
            read_handle,
            result
        );
        result
    }

    /// Calls [`Runtime::channel_read`] using the Node's privilege.
    pub fn channel_read_with_downgrade(
        &self,
        read_handle: oak_abi::Handle,
    ) -> Result<Option<NodeMessage>, OakStatus> {
        debug!(
            "{:?}: channel_read_with_downgrade({})",
            self.node_id, read_handle,
        );
        let result = self
            .runtime
            .channel_read(self.node_id, read_handle, Downgrading::Yes);
        debug!(
            "{:?}: channel_read_with_downgrade({}) -> {:?}",
            self.node_id, read_handle, result
        );
        result
    }

    /// Calls [`Runtime::channel_try_read_message`] without the Node's privilege.
    pub fn channel_try_read_message(
        &self,
        read_handle: oak_abi::Handle,
        bytes_capacity: usize,
        handles_capacity: usize,
    ) -> Result<Option<NodeReadStatus>, OakStatus> {
        debug!(
            "{:?}: channel_try_read({}, bytes_capacity={}, handles_capacity={})",
            self.get_debug_id(),
            read_handle,
            bytes_capacity,
            handles_capacity
        );
        let result = self.runtime.channel_try_read_message(
            self.node_id,
            read_handle,
            bytes_capacity,
            handles_capacity,
            Downgrading::No,
        );
        debug!(
            "{:?}: channel_try_read({}, bytes_capacity={}, handles_capacity={}) -> {:?}",
            self.get_debug_id(),
            read_handle,
            bytes_capacity,
            handles_capacity,
            result
        );
        result
    }

    /// Calls [`Runtime::channel_try_read_message`] using the Node's privilege.
    pub fn channel_try_read_message_with_downgrade(
        &self,
        read_handle: oak_abi::Handle,
        bytes_capacity: usize,
        handles_capacity: usize,
    ) -> Result<Option<NodeReadStatus>, OakStatus> {
        debug!(
            "{:?}: channel_try_read_message_with_downgrade({}, bytes_capacity={}, handles_capacity={})",
            self.get_debug_id(),
            read_handle,
            bytes_capacity,
            handles_capacity
        );
        let result = self.runtime.channel_try_read_message(
            self.node_id,
            read_handle,
            bytes_capacity,
            handles_capacity,
            Downgrading::Yes,
        );
        debug!(
            "{:?}: channel_try_read_message_with_downgrade({}, bytes_capacity={}, handles_capacity={}) -> {:?}",
            self.get_debug_id(),
            read_handle,
            bytes_capacity,
            handles_capacity,
            result
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
            self.get_debug_id(),
            handle,
            capacity
        );
        let result = self
            .runtime
            .get_serialized_channel_label(self.node_id, handle, capacity);
        debug!(
            "{:?}: get_serialized_channel_label({}, capacity={}) -> {:?}",
            self.get_debug_id(),
            handle,
            capacity,
            result
        );
        result
    }

    /// See [`Runtime::get_serialized_node_label`].
    pub fn get_serialized_node_label(&self, capacity: usize) -> Result<LabelReadStatus, OakStatus> {
        debug!(
            "{:?}: get_serialized_node_label(capacity={})",
            self.get_debug_id(),
            capacity
        );
        let result = self
            .runtime
            .get_serialized_node_label(self.node_id, capacity);
        debug!(
            "{:?}: get_serialized_node_label(capacity={}) -> {:?}",
            self.get_debug_id(),
            capacity,
            result
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
            self.get_debug_id(),
            capacity
        );
        let result = self
            .runtime
            .get_serialized_node_privilege(self.node_id, capacity);
        debug!(
            "{:?}: get_serialized_node_privilege(capacity={}) -> {:?}",
            self.get_debug_id(),
            capacity,
            result
        );
        result
    }

    /// See [`Runtime::get_channel_label`].
    pub fn get_channel_label(&self, handle: oak_abi::Handle) -> Result<Label, OakStatus> {
        debug!("{:?}: get_channel_label({})", self.get_debug_id(), handle);
        let result = self.runtime.get_channel_label(self.node_id, handle);
        debug!(
            "{:?}: get_channel_label({}) -> {:?}",
            self.get_debug_id(),
            handle,
            result
        );
        result
    }

    fn get_debug_id(&self) -> String {
        construct_debug_id(&self.node_name, self.node_id)
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

    /// Gets the instance for the current thread.
    ///
    /// Panics if no instance is set for the current thread.
    pub fn current() -> Self {
        RUNTIME_PROXY.with(|proxy| {
            proxy
                .borrow()
                .as_ref()
                .expect("No RuntimeProxy configured for the current thread")
                .clone()
        })
    }

    /// Binds this instance to the current thread.
    ///
    /// This function should be invoked immediately after creating a new thread that may `Clone` or
    /// `Drop` handle types, such as `Sender`s or `Receiver`s.
    ///
    /// In particular, make sure to call this when a new node is created.
    pub fn set_as_current(&self) {
        RUNTIME_PROXY.with(|proxy| {
            proxy.replace(Some(self.clone()));
        })
    }
}

std::thread_local! {
    /// Reference to the [`RuntimeProxy`] bound to the current thread.
    ///
    /// Access this through [`RuntimeProxy::current`], assign it with [`RuntimeProxy::set_as_current`].
    static RUNTIME_PROXY: RefCell<Option<RuntimeProxy>> = RefCell::new(None);
}

// Called by `oak_io` when `clone()` is called on a [`oak_abi::Handle`].
#[no_mangle]
extern "C" fn handle_clone(
    handle: oak_abi::Handle,
    cloned_handle_out: *mut oak_abi::Handle,
) -> u32 {
    match RuntimeProxy::current().handle_clone(handle) {
        Ok(cloned_handle) => {
            unsafe {
                *cloned_handle_out = cloned_handle;
            }
            OakStatus::Ok as u32
        }
        Err(e) => e as u32,
    }
}

// Called by `oak_io` when `drop()` is called on a [`oak_abi::Handle`].
#[no_mangle]
extern "C" fn channel_close(handle: oak_abi::Handle) -> u32 {
    match RuntimeProxy::current().channel_close(handle) {
        Ok(()) => OakStatus::Ok as u32,
        Err(e) => e as u32,
    }
}
