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

use std::prelude::v1::*;

use std::collections::HashMap;
use std::string::String;
use std::sync::Arc;

use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering::SeqCst;

use log::error;

use oak_abi::OakStatus;

use crate::channel;
use crate::channel::{ChannelReader, ChannelWriter};
use crate::node::{load_wasm, NodeConfiguration};
use crate::platform;
use crate::proto;
use crate::proto::manager::NodeConfiguration_oneof_config_type;

/// Runtime structure for configuring and running a set of Oak nodes.
pub struct Runtime {
    configurations: HashMap<String, NodeConfiguration>,
    terminating: AtomicBool,
    node_threads: platform::Mutex<Vec<platform::JoinHandle>>,
}

impl Runtime {
    /// Configure and run the protobuf specified `ApplicationConfiguration`. After creating a
    /// `Runtime` calling `stop` will send termination signals to nodes and wait for them to
    /// terminate.
    pub fn configure_and_run(
        app_config: proto::manager::ApplicationConfiguration,
    ) -> Result<(RuntimeRef, ChannelWriter), OakStatus> {
        let mut runtime = Runtime {
            configurations: HashMap::new(),
            terminating: AtomicBool::new(false),
            node_threads: platform::Mutex::new(Vec::new()),
        };

        for config in app_config.get_node_configs() {
            runtime.configurations.insert(
                config.name.clone(),
                match &config.config_type {
                    None => {
                        error!("Node config {} with no type", config.name);
                        return Err(OakStatus::ERR_INVALID_ARGS);
                    }
                    Some(NodeConfiguration_oneof_config_type::log_config(_)) => {
                        NodeConfiguration::LogNode
                    }
                    Some(NodeConfiguration_oneof_config_type::wasm_config(
                        proto::manager::WebAssemblyConfiguration { module_bytes, .. },
                    )) => load_wasm(&module_bytes).map_err(|e| {
                        error!("Error loading Wasm module: {}", e);
                        OakStatus::ERR_INVALID_ARGS
                    })?,
                    Some(_) => {
                        error!("Pseudo-node not implemented!");
                        return Err(OakStatus::ERR_INVALID_ARGS);
                    }
                },
            );
        }

        let runtime = RuntimeRef(Arc::new(runtime));
        let (chan_writer, chan_reader) = channel::new();

        runtime.node_create(
            &app_config.initial_node_config_name,
            &app_config.initial_entrypoint_name,
            chan_reader,
        )?;

        Ok((runtime, chan_writer))
    }

    /// Thread safe method for determining if the `Runtime` is terminating.
    pub fn is_terminating(&self) -> bool {
        self.terminating.load(SeqCst)
    }

    /// Thread safe method for signaling termination to a `Runtime` and waiting for its node
    /// threads to terminate.
    pub fn stop(&self) {
        let handles = {
            let mut node_threads = self.node_threads.lock().unwrap();
            self.terminating.store(true, SeqCst);

            std::mem::replace(&mut *node_threads, vec![])
        };

        for handle in handles {
            handle.join().expect("Failed to join handle");
        }
    }
}

/// A reference to a `Runtime`
#[derive(Clone)]
pub struct RuntimeRef(Arc<Runtime>);

impl RuntimeRef {
    /// Thread safe method that attempts to create a node within the `Runtime` corresponding to a
    /// given module name and entrypoint. The `reader: ChannelReader` is passed to the newly
    /// created node.
    ///
    /// `node_create` is a method of `RuntimeRef` and not `Runtime`, so that the underlying
    /// `Arc<Runtime>` can be passed to `conf.new_instance` and given to a new node thread.
    pub fn node_create(
        &self,
        module_name: &str,
        entrypoint: &str,
        reader: ChannelReader,
    ) -> Result<(), OakStatus> {
        if self.is_terminating() {
            return Err(OakStatus::ERR_TERMINATED);
        }

        let mut node_threads = self.node_threads.lock().unwrap();

        if self.is_terminating() {
            return Err(OakStatus::ERR_TERMINATED);
        }

        let join_handle = self
            .configurations
            .get(module_name)
            .ok_or(OakStatus::ERR_INVALID_ARGS)
            .and_then(|conf| {
                conf.new_instance(module_name, self.clone(), entrypoint.to_owned(), reader)
            })?;
        node_threads.push(join_handle);

        Ok(())
    }
}

impl std::ops::Deref for RuntimeRef {
    type Target = Runtime;

    #[inline]
    fn deref(&self) -> &Runtime {
        &self.0
    }
}
